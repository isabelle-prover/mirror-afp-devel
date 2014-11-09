section {* The weak simulation *}

theory WeakSimulation imports Slice begin

context SDG begin

lemma call_node_notin_slice_return_node_neither:
  assumes "call_of_return_node n n'" and "n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "n \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
proof -
  from `call_of_return_node n n'` obtain a a' where "return_node n"
    and "valid_edge a" and "n' = sourcenode a"
    and "valid_edge a'" and "a' \<in> get_return_edges a" 
    and "n = targetnode a'" by(fastforce simp:call_of_return_node_def)
  from `valid_edge a` `a' \<in> get_return_edges a` obtain Q p r fs 
    where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by(fastforce dest!:only_call_get_return_edges)
  with `valid_edge a` `a' \<in> get_return_edges a` obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    by(fastforce dest!:call_return_edges)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
  have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')"
    by(fastforce intro:sum_SDG_call_summary_edge)
  show ?thesis
  proof
    assume "n \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    with `n = targetnode a'` have "CFG_node (targetnode a') \<in> HRB_slice S"
      by(simp add:SDG_to_CFG_set_def)
    hence "CFG_node (sourcenode a) \<in> HRB_slice S"
    proof(induct "CFG_node (targetnode a')" rule:HRB_slice_cases)
      case (phase1 nx)
      with `CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')`
      show ?case by(fastforce intro:combine_SDG_slices.combSlice_refl sum_slice1 
                              simp:HRB_slice_def)
    next
      case (phase2 nx n' n'' p')
      from `CFG_node (targetnode a') \<in> sum_SDG_slice2 n'` 
        `CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')` `valid_edge a`
      have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 n'"
        by(fastforce intro:sum_slice2)
      with `n' \<in> sum_SDG_slice1 nx` `n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')` `nx \<in> S`
      show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node
                              simp:HRB_slice_def)
    qed
    with `n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `n' = sourcenode a` show False 
      by(simp add:SDG_to_CFG_set_def HRB_slice_def)
  qed
qed


lemma edge_obs_intra_slice_eq:
assumes "valid_edge a" and "intra_kind (kind a)" and "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
         obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
proof -
  from assms have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subseteq>
                   obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(rule edge_obs_intra_subset)
  from `valid_edge a` have "valid_node (sourcenode a)" by simp
  { fix x assume "x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
    have "\<exists>as. targetnode a -as\<rightarrow>\<^sub>\<iota>* x"
    proof(cases "method_exit x")
      case True
      from `valid_edge a` have "valid_node (targetnode a)" by simp
      then obtain asx where "targetnode a -asx\<rightarrow>\<^sub>\<surd>* (_Exit_)" 
        by(fastforce dest:Exit_path)
      then obtain as pex where "targetnode a -as\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
        by -(erule valid_Exit_path_intra_path)
      hence "get_proc pex = get_proc (targetnode a)"
        by -(rule intra_path_get_procs[THEN sym])
      also from `valid_edge a` `intra_kind (kind a)` 
      have "\<dots> = get_proc (sourcenode a)"
        by -(rule get_proc_intra[THEN sym])
      also from `x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` True
      have "\<dots> = get_proc x"
        by(fastforce elim:obs_intraE intro:intra_path_get_procs)
      finally have "pex = x" using `method_exit pex` True
        by -(rule method_exit_unique)
      with `targetnode a -as\<rightarrow>\<^sub>\<iota>* pex` show ?thesis by fastforce
    next
      case False
      with `x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "x postdominates (sourcenode a)" by(rule obs_intra_postdominate)
      with `valid_edge a` `intra_kind (kind a)` `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "x postdominates (targetnode a)"
        by(fastforce elim:postdominate_inner_path_targetnode path_edge obs_intraE 
                    simp:intra_path_def sourcenodes_def)
      thus ?thesis by(fastforce elim:postdominate_implies_inner_path)
    qed
    then obtain as where "targetnode a -as\<rightarrow>\<^sub>\<iota>* x" by blast
    from `x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "x \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by -(erule obs_intraE)
    have "\<exists>x' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>. \<exists>as'. targetnode a -as'\<rightarrow>\<^sub>\<iota>* x' \<and> 
      (\<forall>a' \<in> set (sourcenodes as'). a' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    proof(cases "\<exists>a' \<in> set (sourcenodes as). a' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      then obtain zs z zs' where "sourcenodes as = zs@z#zs'"
        and "z \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "\<forall>z' \<in> set zs. z' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(erule split_list_first_propE)
      then obtain ys y ys'
        where "sourcenodes ys = zs" and "as = ys@y#ys'"
        and "sourcenode y = z"
        by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
      from `targetnode a -as\<rightarrow>\<^sub>\<iota>* x` `as = ys@y#ys'`
      have "targetnode a -ys@y#ys'\<rightarrow>* x" and "\<forall>y' \<in> set ys. intra_kind (kind y')"
        by(simp_all add:intra_path_def)
      from `targetnode a -ys@y#ys'\<rightarrow>* x` have "targetnode a -ys\<rightarrow>* sourcenode y"
        by(rule path_split)
      with `\<forall>y' \<in> set ys. intra_kind (kind y')` `sourcenode y = z`
        `\<forall>z' \<in> set zs. z' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `z \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `sourcenodes ys = zs`
      show ?thesis by(fastforce simp:intra_path_def)
    next
      case False
      with `targetnode a -as\<rightarrow>\<^sub>\<iota>* x` `x \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      show ?thesis by fastforce
    qed
    hence "\<exists>y. y \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce intro:obs_intra_elem)
    with `obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` 
    have False by simp }
  with `obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subseteq>
        obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `valid_node (sourcenode a)`
  show ?thesis by(cases "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}") 
                 (auto dest!:obs_intra_singleton_disj)
qed


lemma intra_edge_obs_slice:
  assumes "ms \<noteq> []" and "ms'' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "valid_edge a" 
  and "intra_kind (kind a)" 
  and disj:"(\<exists>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
                               m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "hd ms = sourcenode a" and "ms' = targetnode a#tl ms" 
  and "\<forall>n \<in> set (tl ms'). return_node n"
  shows "ms'' \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
proof -
  from `ms'' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `\<forall>n \<in> set (tl ms'). return_node n`
  obtain msx m msx' mx m' where "ms' = msx@m#msx'" and "ms'' = mx#msx'"
    and "mx \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and imp:"\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
    \<longrightarrow> (\<exists>x'' \<in> set (xs'@[m]). \<exists>mx. call_of_return_node x'' mx \<and> 
                                   mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(erule obsE)
  show ?thesis
  proof(cases msx)
    case Nil
    with `\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      disj `ms' = msx@m#msx'` `hd ms = sourcenode a` `ms' = targetnode a#tl ms`
    have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(cases ms) auto
    from `ms' = msx@m#msx'` `ms' = targetnode a#tl ms` Nil 
    have "m = targetnode a" by simp
    with `valid_edge a` `intra_kind (kind a)` `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `mx \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "mx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce dest:edge_obs_intra_subset)
    from `ms' = msx@m#msx'` Nil `ms' = targetnode a # tl ms` 
      `hd ms = sourcenode a` `ms \<noteq> []`
    have "ms = []@sourcenode a#msx'" by(cases ms) auto
    with `ms'' = mx#msx'` `mx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`  
      `\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` Nil
    show ?thesis by(fastforce intro!:obsI)
  next
    case (Cons x xs)
    with `ms' = msx@m#msx'` `ms' = targetnode a # tl ms`
    have "msx = targetnode a#xs" by simp
    from Cons `ms' = msx@m#msx'` `ms' = targetnode a # tl ms` `hd ms = sourcenode a`
    have "ms = (sourcenode a#xs)@m#msx'" by(cases ms) auto
    from disj `ms = (sourcenode a#xs)@m#msx'` 
      `\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have disj2:"(\<exists>m \<in> set (xs@[m]). \<exists>m'. call_of_return_node m m' \<and> 
                            m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by fastforce
    hence "\<forall>zs z zs'. sourcenode a#xs = zs@z#zs' \<and> obs_intra z \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
      \<longrightarrow> (\<exists>z'' \<in> set (zs'@[m]). \<exists>mx. call_of_return_node z'' mx \<and> 
                                   mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    proof(cases "hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      with `hd ms = sourcenode a` have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      with `valid_edge a` `intra_kind (kind a)`
      have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
        obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(rule edge_obs_intra_slice_eq)
      with imp `msx = targetnode a#xs` show ?thesis
        by auto(case_tac zs,fastforce,erule_tac x="targetnode a#list" in allE,fastforce)
    next
      case False
      with `hd ms = sourcenode a` `valid_edge a` 
      have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
        by(fastforce intro!:n_in_obs_intra)
      from False disj2 
      have "\<exists>m \<in> set (xs@[m]). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by simp
      with imp `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}`
        `msx = targetnode a#xs` show ?thesis
        by auto(case_tac zs,fastforce,erule_tac x="targetnode a#list" in allE,fastforce)
    qed
    with `ms' = msx@m#msx'` `ms' = targetnode a # tl ms` `hd ms = sourcenode a`
      `ms'' = mx#msx'` `mx \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
      `\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `ms = (sourcenode a#xs)@m#msx'`
    show ?thesis by(simp del:obs.simps)(rule obsI,auto)
  qed
qed



subsection {* Silent moves *}

inductive silent_move :: 
  "'node SDG_node set \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
  (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge \<Rightarrow> 'node list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') -_\<rightarrow>\<^sub>\<tau> '(_,_')" [51,50,0,0,50,0,0] 51) 

where silent_move_intra:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; intra_kind(kind a);
    (\<exists>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
    hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; \<forall>m \<in> set (tl ms). return_node m;
    length s' = length s; length ms = length s;
    hd ms = sourcenode a; ms' = (targetnode a)#tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')"

  | silent_move_call:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; 
    valid_edge a'; a' \<in> get_return_edges a;
    (\<exists>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
    hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; \<forall>m \<in> set (tl ms). return_node m;
    length ms = length s; length s' = Suc(length s); 
    hd ms = sourcenode a; ms' = (targetnode a)#(targetnode a')#tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')"

  | silent_move_return:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'; 
    \<exists>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
    \<forall>m \<in> set (tl ms). return_node m; length ms = length s; length s = Suc(length s');
    s' \<noteq> []; hd ms = sourcenode a; hd(tl ms) = targetnode a; ms' = tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')"


lemma silent_move_valid_nodes:
  "\<lbrakk>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s'); \<forall>m \<in> set ms'. valid_node m\<rbrakk>
  \<Longrightarrow> \<forall>m \<in> set ms. valid_node m"
by(induct rule:silent_move.induct)(case_tac ms,auto)+


lemma silent_move_return_node:
  "S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s') \<Longrightarrow> \<forall>m \<in> set (tl ms'). return_node m"
proof(induct rule:silent_move.induct)
  case (silent_move_intra f a s s' ms n\<^sub>c ms')
  thus ?case by simp
next
  case (silent_move_call f a s s' Q r p fs a' ms n\<^sub>c ms')
  from `valid_edge a'` `valid_edge a` `a' \<in> get_return_edges a`
  have "return_node (targetnode a')" by(fastforce simp:return_node_def)
  with `\<forall>m\<in>set (tl ms). return_node m` `ms' = targetnode a # targetnode a' # tl ms`
  show ?case by simp
next
  case (silent_move_return f a s s' Q p f' ms n\<^sub>c ms')
  thus ?case by(cases "tl ms") auto
qed


lemma silent_move_equal_length:
  assumes "S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')" 
  shows "length ms = length s" and "length ms' = length s'"
proof -
  from `S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')`
  have "length ms = length s \<and> length ms' = length s'"
  proof(induct rule:silent_move.induct)
    case (silent_move_intra f a s s' ms n\<^sub>c ms')
    from `pred (f a) s` obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
    from `length ms = length s` `ms' = targetnode a # tl ms`
      `length s' = length s` show ?case by simp
  next
    case (silent_move_call f a s s' Q r p fs a' ms n\<^sub>c ms')
    from `pred (f a) s` obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
    from `length ms = length s` `length s' = Suc (length s)` 
      `ms' = targetnode a # targetnode a' # tl ms` show ?case by simp
  next
    case (silent_move_return f a s s' Q p f' ms n\<^sub>c ms')
    from `length ms = length s` `length s = Suc (length s')` `ms' = tl ms` `s' \<noteq> []`
    show ?case by simp
  qed
  thus "length ms = length s" and "length ms' = length s'" by simp_all
qed


lemma silent_move_obs_slice:
  "\<lbrakk>S,kind \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s'); msx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; 
    \<forall>n \<in> set (tl ms'). return_node n\<rbrakk>
  \<Longrightarrow> msx \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
proof(induct S f\<equiv>"kind" ms s a ms' s' rule:silent_move.induct)
  case (silent_move_intra a s s' ms n\<^sub>c ms')
  from `pred (kind a) s` `length ms = length s` have "ms \<noteq> []"
    by(cases s) auto
  with silent_move_intra show ?case by -(rule intra_edge_obs_slice)
next
  case (silent_move_call a s s' Q r p fs a' ms S ms')
  note disj = `(\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
    m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
  from `valid_edge a'` `valid_edge a` `a' \<in> get_return_edges a`
  have "return_node (targetnode a')" by(fastforce simp:return_node_def)
  with `valid_edge a` `a' \<in> get_return_edges a` `valid_edge a'`
  have "call_of_return_node (targetnode a') (sourcenode a)"
    by(simp add:call_of_return_node_def) blast
  from `pred (kind a) s` `length ms = length s`
  have "ms \<noteq> []" by(cases s) auto
  from disj
  show ?case
  proof
    assume "hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    with `hd ms = sourcenode a` have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with `call_of_return_node (targetnode a') (sourcenode a)`
      `ms' = targetnode a # targetnode a' # tl ms`
    have "\<exists>n' \<in> set (tl ms'). \<exists>nx. call_of_return_node n' nx \<and> nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by fastforce
    with `msx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `ms' = targetnode a # targetnode a' # tl ms`
    have "msx \<in> obs (targetnode a' # tl ms) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    from `valid_edge a` `a' \<in> get_return_edges a`
    obtain a'' where "valid_edge a''" and [simp]:"sourcenode a'' = sourcenode a"
      and [simp]:"targetnode a'' = targetnode a'" and "intra_kind(kind a'')"
      by -(drule call_return_node_edge,auto simp:intra_kind_def)
    from `\<forall>m\<in>set (tl ms'). return_node m` `ms' = targetnode a # targetnode a' # tl ms`
    have "\<forall>m\<in>set (tl ms). return_node m" by simp
    with `ms \<noteq> []` `msx \<in> obs (targetnode a'#tl ms) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `valid_edge a''` `intra_kind(kind a'')` disj
      `hd ms = sourcenode a`
    show ?case by -(rule intra_edge_obs_slice,fastforce+)
  next
    assume "\<exists>m\<in>set (tl ms).
      \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    with `ms \<noteq> []` `msx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `ms' = targetnode a # targetnode a' # tl ms`
    show ?thesis by(cases ms) auto
  qed
next
  case (silent_move_return a s s' Q p f' ms S ms')
  from `length ms = length s` `length s = Suc (length s')` `s' \<noteq> []`
  have "ms \<noteq> []" and "tl ms \<noteq> []" by(auto simp:length_Suc_conv)
  from `\<exists>m\<in>set (tl ms).
    \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    `tl ms \<noteq> []` `hd (tl ms) = targetnode a`
  have "(\<exists>m'. call_of_return_node (targetnode a) m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
    (\<exists>m\<in>set (tl (tl ms)). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(cases "tl ms") auto
  hence "obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs (tl ms) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  proof
    assume "\<exists>m'. call_of_return_node (targetnode a) m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    from `tl ms \<noteq> []` have "hd (tl ms) \<in> set (tl ms)" by simp
    with `hd (tl ms) = targetnode a` have "targetnode a \<in> set (tl ms)" by simp
    with `ms \<noteq> []` 
      `\<exists>m'. call_of_return_node (targetnode a) m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
      m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(cases ms) auto
    with `ms \<noteq> []` show ?thesis by(cases ms) auto
  next
    assume "\<exists>m\<in>set (tl (tl ms)). \<exists>m'. call_of_return_node m m' \<and> 
      m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    with `ms \<noteq> []` `tl ms \<noteq> []` show ?thesis
      by(cases ms,auto simp:Let_def)(case_tac list,auto)+
  qed
  with `ms' = tl ms` `msx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` show ?case by simp
qed



lemma silent_move_empty_obs_slice:
  assumes "S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')" and "obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
  shows "obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
proof(rule ccontr)
  assume "obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
  then obtain xs where "xs \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
  from `S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')`
  have "\<forall>m \<in> set (tl ms). return_node m"
    by(fastforce elim!:silent_move.cases simp:call_of_return_node_def)
  with `xs \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
  obtain msx m msx' m' where assms:"ms = msx@m#msx'" "xs = m'#msx'"
    "m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    "\<forall>mx \<in> set msx'. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
    \<longrightarrow> (\<exists>x'' \<in> set (xs'@[m]). \<exists>mx. call_of_return_node x'' mx \<and> 
                              mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(erule obsE)
  from `S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')` `obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` assms
  show False
  proof(induct rule:silent_move.induct)
    case (silent_move_intra f a s s' ms S ms')
    note disj = `(\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
      m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    note msx = `\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
      (\<exists>x''\<in>set (xs' @ [m]). \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
    note msx' = `\<forall>mx\<in>set msx'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    show False
    proof(cases msx)
      case Nil
      with `ms = msx @ m # msx'` `hd ms = sourcenode a` have [simp]:"m = sourcenode a"
        and "tl ms = msx'" by simp_all
      from Nil `ms' = targetnode a # tl ms` `ms = msx @ m # msx'`
      have "ms' = msx @ targetnode a # msx'" by simp
      from msx' disj `tl ms = msx'` `hd ms = sourcenode a`
      have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      with `valid_edge a` `intra_kind (kind a)`
      have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> =
        obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(rule edge_obs_intra_slice_eq)
      with `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "m' \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from msx Nil have "\<forall>xs x xs'. msx = xs@x#xs' \<and>  
        obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
        (\<exists>x''\<in>set (xs' @ [targetnode a]). \<exists>mx. call_of_return_node x'' mx \<and> 
        mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)" by simp
      with `m' \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` msx' 
        `ms' = msx @ targetnode a # msx'`
      have "m'#msx' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(rule obsI)
      with `obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` show False by simp
    next
      case (Cons y ys)
      with `ms = msx @ m # msx'` `ms' = targetnode a # tl ms` `hd ms = sourcenode a`
      have "ms' = targetnode a # ys @ m # msx'" and "y = sourcenode a" 
        and "tl ms = ys @ m # msx'" by simp_all
      { fix x assume "x \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
        proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
          case True
          from `valid_edge a` have "valid_node (sourcenode a)" by simp
          from this True 
          have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
            by(rule n_in_obs_intra)
          thus ?thesis by simp
        next
          case False
          from `valid_edge a` `intra_kind (kind a)` False
          have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
            obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
            by(rule edge_obs_intra_slice_eq)
          with `x \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` show ?thesis
            by fastforce
        qed }
      with msx Cons `y = sourcenode a` 
      have "\<forall>xs x xs'. targetnode a # ys = xs@x#xs' \<and> 
        obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> (\<exists>x''\<in>set (xs' @ [m]). 
        \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
        apply clarsimp apply(case_tac xs) apply auto
        apply(erule_tac x="[]" in allE) apply clarsimp
        apply(erule_tac x="sourcenode a # list" in allE) apply auto
        done
      with `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` msx' 
        `ms' = targetnode a # ys @ m # msx'`
      have "m'#msx' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by -(rule obsI,auto)
      with `obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` show False by simp
    qed
  next
    case (silent_move_call f a s s' Q r p fs a' ms S ms')
    note disj = `(\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
      m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    note msx = `\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
      (\<exists>x''\<in>set (xs' @ [m]). \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
    note msx' = `\<forall>mx\<in>set msx'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    from `valid_edge a` `a' \<in> get_return_edges a` obtain a'' where "valid_edge a''"
      and "sourcenode a'' = sourcenode a" and "targetnode a'' = targetnode a'"
      and "intra_kind (kind a'')" 
      by(fastforce dest:call_return_node_edge simp:intra_kind_def)
    from `valid_edge a'` `valid_edge a` `a' \<in> get_return_edges a`
    have "call_of_return_node (targetnode a') (sourcenode a)"
      by(fastforce simp:call_of_return_node_def return_node_def)
    show False
    proof(cases msx)
      case Nil
      with `ms = msx @ m # msx'` `hd ms = sourcenode a` have [simp]:"m = sourcenode a"
        and "tl ms = msx'" by simp_all
      from Nil `ms' = targetnode a # targetnode a' # tl ms` `ms = msx @ m # msx'`
      have "ms' = targetnode a # targetnode a' # msx'" by simp
      from msx' disj `tl ms = msx'` `hd ms = sourcenode a`
      have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      from `valid_edge a''` `intra_kind (kind a'')` `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `sourcenode a'' = sourcenode a` `targetnode a'' = targetnode a'`
      have "obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
         obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(fastforce dest:edge_obs_intra_slice_eq)
      with `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
      have "m' \<in> obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from this msx' have "m'#msx' \<in> obs (targetnode a'#msx') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(fastforce intro:obsI)
      from `call_of_return_node (targetnode a') (sourcenode a)`
        `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "\<exists>m' \<in> set (targetnode a'#msx').
        \<exists>mx. call_of_return_node m' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by fastforce
      with `m'#msx' \<in> obs (targetnode a'#msx') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "m'#msx' \<in> obs (targetnode a#targetnode a'#msx') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by simp
      with `ms' = targetnode a # targetnode a' # msx'` `obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
      show False by simp
    next
      case (Cons y ys)
      with `ms = msx @ m # msx'` `ms' = targetnode a # targetnode a' # tl ms` 
        `hd ms = sourcenode a`
      have "ms' = targetnode a # targetnode a' # ys @ m # msx'" 
        and "y = sourcenode a" and "tl ms = ys @ m # msx'" by simp_all
      show False
      proof(cases "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
          (\<exists>x''\<in>set (targetnode a' # ys @ [m]).
          \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)")
        case True
        hence imp:"obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow>
          (\<exists>x''\<in>set (targetnode a' # ys @ [m]).
          \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)" .
        show False
        proof(cases "obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
            (\<exists>x''\<in>set (ys @ [m]). \<exists>mx. call_of_return_node x'' mx \<and> 
            mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)")
          case True
          with imp msx Cons `y = sourcenode a` 
          have "\<forall>xs x xs'. targetnode a # targetnode a' # ys = xs@x#xs' \<and> 
            obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> (\<exists>x''\<in>set (xs' @ [m]). 
            \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
            apply clarsimp apply(case_tac xs) apply fastforce
            apply(case_tac list) apply fastforce apply clarsimp
            apply(erule_tac x="sourcenode a # lista" in allE) apply auto
            done
          with `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` msx' 
            `ms' = targetnode a # targetnode a' # ys @ m # msx'`
          have "m'#msx' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by -(rule obsI,auto)
          with `obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` show False by simp
        next
          case False
          hence "obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
            and all:"\<forall>x''\<in>set (ys @ [m]). \<forall>mx. call_of_return_node x'' mx \<longrightarrow> 
            mx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
            by fastforce+
          have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
          proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
            case True
            from `valid_edge a` have "valid_node (sourcenode a)" by simp
            from this True 
            have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
              by(rule n_in_obs_intra)
            thus ?thesis by simp
          next
            case False
            with `sourcenode a'' = sourcenode a`
            have "sourcenode a'' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
            with `valid_edge a''` `intra_kind (kind a'')`
            have "obs_intra (targetnode a'') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
              obs_intra (sourcenode a'') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
              by(rule edge_obs_intra_slice_eq)
            with `obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}` 
              `sourcenode a'' = sourcenode a` `targetnode a'' = targetnode a'`
            show ?thesis by fastforce 
          qed
          with msx Cons `y = sourcenode a` all
          show False by simp blast
        qed
      next
        case False
        hence "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
          and all:"\<forall>x''\<in>set (targetnode a' # ys @ [m]). 
          \<forall>mx. call_of_return_node x'' mx \<longrightarrow> mx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          by fastforce+
        with Cons `y = sourcenode a` msx 
        have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" by auto blast
        from `call_of_return_node (targetnode a') (sourcenode a)` all
        have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
        from `valid_edge a` have "valid_node (sourcenode a)" by simp
        from this `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
        have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
          by(rule n_in_obs_intra)
        with `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` show False by simp
      qed
    qed
  next
    case (silent_move_return f a s s' Q p f' ms S ms')
    note msx = `\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
      (\<exists>x''\<in>set (xs' @ [m]). \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
    note msx' = `\<forall>mx\<in>set msx'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    show False
    proof(cases msx)
      case Nil
      with `ms = msx @ m # msx'` `hd ms = sourcenode a` have  "tl ms = msx'" by simp
      with `\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        msx'
      show False by fastforce
    next
      case (Cons y ys)
      with `ms = msx @ m # msx'` `hd ms = sourcenode a` `ms' = tl ms`
      have "ms' = ys @ m # msx'" and "y = sourcenode a" by simp_all
      from msx Cons have "\<forall>xs x xs'. ys = xs@x#xs' \<and> 
        obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow>  (\<exists>x''\<in>set (xs' @ [m]). 
        \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
        by auto (erule_tac x="y # xs" in allE,auto)
      with `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` msx' `ms' = ys @ m # msx'`
      have "m'#msx' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(rule obsI)
      with `obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` show False by simp
    qed
  qed
qed



inductive silent_moves :: 
  "'node SDG_node set \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
  (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge list \<Rightarrow> 'node list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') =_\<Rightarrow>\<^sub>\<tau> '(_,_')" [51,50,0,0,50,0,0] 51)

  where silent_moves_Nil: "length ms = length s \<Longrightarrow> S,f \<turnstile> (ms,s) =[]\<Rightarrow>\<^sub>\<tau> (ms,s)"

  | silent_moves_Cons:
  "\<lbrakk>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s'); S,f \<turnstile> (ms',s') =as\<Rightarrow>\<^sub>\<tau> (ms'',s'')\<rbrakk> 
  \<Longrightarrow> S,f \<turnstile> (ms,s) =a#as\<Rightarrow>\<^sub>\<tau> (ms'',s'')"


lemma silent_moves_equal_length:
  assumes "S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')" 
  shows "length ms = length s" and "length ms' = length s'"
proof -
  from `S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')` 
  have "length ms = length s \<and> length ms' = length s'"
  proof(induct rule:silent_moves.induct)
    case (silent_moves_Cons S f ms s a ms' s' as ms'' s'')
    from `S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')`
    have "length ms = length s" and "length ms' = length s'" 
      by(rule silent_move_equal_length)+
    with `length ms' = length s' \<and> length ms'' = length s''`
    show ?case by simp
  qed simp
  thus "length ms = length s" "length ms' = length s'" by simp_all
qed


lemma silent_moves_Append:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms'',s''); S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (ms,s) =as@as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
by(induct rule:silent_moves.induct)(auto intro:silent_moves.intros)


lemma silent_moves_split:
  assumes "S,f \<turnstile> (ms,s) =as@as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
  obtains ms'' s'' where "S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms'',s'')"
  and "S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
proof(atomize_elim)
  from `S,f \<turnstile> (ms,s) =as@as'\<Rightarrow>\<^sub>\<tau> (ms',s')`
  show "\<exists>ms'' s''. S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms'',s'') \<and> S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
  proof(induct as arbitrary:ms s)
    case Nil
    from `S,f \<turnstile> (ms,s) =[] @ as'\<Rightarrow>\<^sub>\<tau> (ms',s')` have "length ms = length s"
      by(fastforce intro:silent_moves_equal_length)
    hence "S,f \<turnstile> (ms,s) =[]\<Rightarrow>\<^sub>\<tau> (ms,s)" by(rule silent_moves_Nil)
    with `S,f \<turnstile> (ms,s) =[] @ as'\<Rightarrow>\<^sub>\<tau> (ms',s')` show ?case by fastforce
  next
    case (Cons ax asx)
    note IH = `\<And>ms s. S,f \<turnstile> (ms,s) =asx @ as'\<Rightarrow>\<^sub>\<tau> (ms',s') \<Longrightarrow>
      \<exists>ms'' s''. S,f \<turnstile> (ms,s) =asx\<Rightarrow>\<^sub>\<tau> (ms'',s'') \<and> S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')`
    from `S,f \<turnstile> (ms,s) =(ax # asx) @ as'\<Rightarrow>\<^sub>\<tau> (ms',s')`
    obtain msx sx where "S,f \<turnstile> (ms,s) -ax\<rightarrow>\<^sub>\<tau> (msx,sx)"
      and "S,f \<turnstile> (msx,sx) =asx @ as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
      by(auto elim:silent_moves.cases)
    from IH[OF this(2)] obtain ms'' s'' where "S,f \<turnstile> (msx,sx) =asx\<Rightarrow>\<^sub>\<tau> (ms'',s'')"
      and "S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')" by blast
    from `S,f \<turnstile> (ms,s) -ax\<rightarrow>\<^sub>\<tau> (msx,sx)` `S,f \<turnstile> (msx,sx) =asx\<Rightarrow>\<^sub>\<tau> (ms'',s'')`
    have "S,f \<turnstile> (ms,s) =ax#asx\<Rightarrow>\<^sub>\<tau> (ms'',s'')" by(rule silent_moves_Cons)
    with `S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')` show ?case by blast
  qed
qed


lemma valid_nodes_silent_moves:
  "\<lbrakk>S,f\<turnstile> (ms,s) =as'\<Rightarrow>\<^sub>\<tau> (ms',s'); \<forall>m \<in> set ms. valid_node m\<rbrakk>
  \<Longrightarrow> \<forall>m \<in> set ms'. valid_node m"
proof(induct rule:silent_moves.induct)
  case (silent_moves_Cons S f ms s a ms' s' as ms'' s'')
  note IH = `\<forall>m\<in>set ms'. valid_node m \<Longrightarrow> \<forall>m\<in>set ms''. valid_node m`
  from `S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')` `\<forall>m\<in>set ms. valid_node m`
  have "\<forall>m\<in>set ms'. valid_node m"
    apply - apply(erule silent_move.cases) apply auto
    by(cases ms,auto dest:get_return_edges_valid)+
  from IH[OF this] show ?case .
qed simp


lemma return_nodes_silent_moves:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as'\<Rightarrow>\<^sub>\<tau> (ms',s'); \<forall>m \<in> set (tl ms). return_node m\<rbrakk>
  \<Longrightarrow> \<forall>m \<in> set (tl ms'). return_node m"
by(induct rule:silent_moves.induct,auto dest:silent_move_return_node)


lemma silent_moves_intra_path:
  "\<lbrakk>S,f \<turnstile> (m#ms,s) =as\<Rightarrow>\<^sub>\<tau> (m'#ms',s'); \<forall>a \<in> set as. intra_kind(kind a)\<rbrakk>
  \<Longrightarrow> ms = ms' \<and> get_proc m = get_proc m'"
proof(induct S f "m#ms" s as "m'#ms'" s' arbitrary:m
  rule:silent_moves.induct)
  case (silent_moves_Cons S f sx a msx' sx' as s'')
  thus ?case
  proof(induct _ _ "m # ms" _ _ _ _ rule:silent_move.induct)
    case (silent_move_intra f a s s' n\<^sub>c msx')
    note IH = `\<And>m. \<lbrakk>msx' = m # ms; \<forall>a\<in>set as. intra_kind (kind a)\<rbrakk>
      \<Longrightarrow> ms = ms' \<and> get_proc m = get_proc m'`
    from `msx' = targetnode a # tl (m # ms)`
    have "msx' = targetnode a # ms" by simp
    from `\<forall>a\<in>set (a # as). intra_kind (kind a)` have "\<forall>a\<in>set as. intra_kind (kind a)"
      by simp
    from IH[OF `msx' = targetnode a # ms` this]
    have "ms = ms'" and "get_proc (targetnode a) = get_proc m'" by simp_all
    moreover
    from `valid_edge a` `intra_kind (kind a)`
    have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
    moreover
    from `hd (m # ms) = sourcenode a` have "m = sourcenode a" by simp
    ultimately show ?case using `ms = ms'` by simp
  qed (auto simp:intra_kind_def)
qed simp


lemma silent_moves_nodestack_notempty: 
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s'); ms \<noteq> []\<rbrakk> \<Longrightarrow> ms' \<noteq> []"
apply(induct S f ms s as ms' s' rule:silent_moves.induct) apply auto
apply(erule silent_move.cases) apply auto
apply(case_tac "tl msa") by auto


lemma silent_moves_obs_slice:
  "\<lbrakk>S,kind \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s'); mx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; 
  \<forall>n \<in> set (tl ms'). return_node n\<rbrakk>
  \<Longrightarrow> mx \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> (\<forall>n \<in> set (tl ms). return_node n)"
proof(induct S f\<equiv>"kind" ms s as ms' s' rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by simp
next
  case (silent_moves_Cons S ms s a ms' s' as ms'' s'')
  note IH = `\<lbrakk>mx \<in> obs ms'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; \<forall>m\<in>set (tl ms''). return_node m\<rbrakk>
    \<Longrightarrow> mx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> (\<forall>m\<in>set (tl ms'). return_node m)`
  from IH[OF `mx \<in> obs ms'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `\<forall>m\<in>set (tl ms''). return_node m`]
  have "mx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "\<forall>m\<in>set (tl ms'). return_node m"
    by simp_all
  with `S,kind \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')`
  have "mx \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(fastforce intro:silent_move_obs_slice)
  moreover
  from `S,kind \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')` have "\<forall>m\<in>set (tl ms). return_node m"
    by(fastforce elim:silent_move.cases)
  ultimately show ?case by simp
qed


lemma silent_moves_empty_obs_slice:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s'); obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<rbrakk>
  \<Longrightarrow> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
proof(induct rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by simp
next
  case (silent_moves_Cons S f ms s a ms' s' as ms'' s'')
  note IH = `obs ms'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {} \<Longrightarrow> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
  from IH[OF `obs ms'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`]
  have "obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" by simp
  with `S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')`
  show ?case by -(rule silent_move_empty_obs_slice,fastforce)
qed


lemma silent_moves_preds_transfers:
  assumes "S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')"
  shows "preds (map f as) s" and "transfers (map f as) s = s'"
proof -
  from `S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')`
  have "preds (map f as) s \<and> transfers (map f as) s = s'"
  proof(induct rule:silent_moves.induct)
    case silent_moves_Nil thus ?case by simp
  next
    case (silent_moves_Cons S f ms s a ms' s' as ms'' s'')
    from `S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')`
    have "pred (f a) s" and "transfer (f a) s = s'" by(auto elim:silent_move.cases)
    with `preds (map f as) s' \<and> transfers (map f as) s' = s''`
    show ?case by fastforce
  qed
  thus "preds (map f as) s" and "transfers (map f as) s = s'" by simp_all
qed



lemma silent_moves_intra_path_obs:
  assumes "m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "length s = length (m#msx')"
  and "\<forall>m \<in> set msx'. return_node m"
  obtains as' where "S,slice_kind S \<turnstile> (m#msx',s) =as'\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
proof(atomize_elim)
  from `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
  obtain as where "m -as\<rightarrow>\<^sub>\<iota>* m'" and "m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by -(erule obs_intraE)
  from `m -as\<rightarrow>\<^sub>\<iota>* m'` obtain x where "distance m m' x" and "x \<le> length as"
    by(erule every_path_distance)
  from `distance m m' x` `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    `length s = length (m#msx')` `\<forall>m \<in> set msx'. return_node m`
  show "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
  proof(induct x arbitrary:m s rule:nat.induct)
    fix m fix s::"(('var \<rightharpoonup> 'val) \<times> 'ret) list"
    assume "distance m m' 0" and "length s = length (m#msx')"
    then obtain as' where "m -as'\<rightarrow>\<^sub>\<iota>* m'" and "length as' = 0"
      by(auto elim:distance.cases)
    hence "m -[]\<rightarrow>\<^sub>\<iota>* m'" by(cases as) auto
    hence [simp]:"m = m'" by(fastforce elim:path.cases simp:intra_path_def)
    with `length s = length (m#msx')`[THEN sym]
    have "S,slice_kind S \<turnstile> (m#msx',s) =[]\<Rightarrow>\<^sub>\<tau> (m#msx',s)" 
      by -(rule silent_moves_Nil)
    thus "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)" by simp blast
  next
    fix x m fix s::"(('var \<rightharpoonup> 'val) \<times> 'ret) list"
    assume "distance m m' (Suc x)" and "m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      and "length s = length (m#msx')" and "\<forall>m \<in> set msx'. return_node m"
      and IH:"\<And>m s. \<lbrakk>distance m m' x; m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
                     length s = length (m#msx'); \<forall>m \<in> set msx'. return_node m\<rbrakk>
      \<Longrightarrow> \<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
    from `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` have "valid_node m"
      by(rule in_obs_intra_valid)
    with `distance m m' (Suc x)` have "m \<noteq> m'"
      by(fastforce elim:distance.cases dest:empty_path simp:intra_path_def)
    have "m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof
      assume isin:"m \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      with `valid_node m` have "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}"
        by(fastforce intro!:n_in_obs_intra)
      with `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m \<noteq> m'` show False by simp
    qed
    from `distance m m' (Suc x)` obtain a where "valid_edge a" and "m = sourcenode a"
      and "intra_kind(kind a)" and "distance (targetnode a) m' x"
      and target:"targetnode a = (SOME mx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               distance (targetnode a') m' x \<and>
                                               valid_edge a' \<and> intra_kind (kind a') \<and> 
                                               targetnode a' = mx)"
      by -(erule distance_successor_distance,simp+)
    from `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
    have "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m'}"
      by(rule obs_intra_singleton_element)
    with `valid_edge a` `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a` `intra_kind(kind a)`
    have disj:"obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {} \<or> 
               obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m'}"
      by -(drule_tac S="\<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" in edge_obs_intra_subset,auto)
    from `intra_kind(kind a)` `length s = length (m#msx')` `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
      `m = sourcenode a`
    have length:"length (transfer (slice_kind S a) s) = length (targetnode a#msx')"
      by(cases s)
    (auto split:split_if_asm simp add:Let_def slice_kind_def intra_kind_def)
    from `distance (targetnode a) m' x` obtain asx where "targetnode a -asx\<rightarrow>\<^sub>\<iota>* m'" 
      and "length asx = x" and "\<forall>as'. targetnode a -as'\<rightarrow>\<^sub>\<iota>* m' \<longrightarrow> x \<le> length as'"
      by(auto elim:distance.cases)
    from `targetnode a -asx\<rightarrow>\<^sub>\<iota>* m'` `m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    obtain mx where "mx \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
      by(erule path_ex_obs_intra)
    with disj have "m' \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
    from IH[OF `distance (targetnode a) m' x` this length 
      `\<forall>m \<in> set msx'. return_node m`]
    obtain asx' where moves:"S,slice_kind S \<turnstile> 
      (targetnode a#msx',transfer (slice_kind S a) s) =asx'\<Rightarrow>\<^sub>\<tau> 
      (m'#msx',transfer (slice_kind S a) s)" by blast
    have "pred (slice_kind S a) s \<and> transfer (slice_kind S a) s = s"
    proof(cases "kind a")
      fix f assume "kind a = \<Up>f"
      with `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a` have "slice_kind S a = \<Up>id"
        by(fastforce intro:slice_kind_Upd)
      with `length s = length (m#msx')` show ?thesis by(cases s) auto
    next
      fix Q assume "kind a = (Q)\<^sub>\<surd>"
      with `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a`
        `m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `distance (targetnode a) m' x`
        `distance m m' (Suc x)` target
      have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
        by(fastforce intro:slice_kind_Pred_obs_nearer_SOME)
      with `length s = length (m#msx')` show ?thesis by(cases s) auto
    next
      fix Q r p fs assume "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      with `intra_kind(kind a)` have False by(simp add:intra_kind_def)
      thus ?thesis by simp
    next
      fix Q p f assume "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      with `intra_kind(kind a)` have False by(simp add:intra_kind_def)
      thus ?thesis by simp
    qed
    hence "pred (slice_kind S a) s" and "transfer (slice_kind S a) s = s"
      by simp_all
    with `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a` `valid_edge a`
      `intra_kind(kind a)` `length s = length (m#msx')` `\<forall>m \<in> set msx'. return_node m`
    have "S,slice_kind S \<turnstile> (sourcenode a#msx',s) -a\<rightarrow>\<^sub>\<tau> 
                             (targetnode a#msx',transfer (slice_kind S a) s)"
      by(fastforce intro:silent_move_intra)
    with moves `transfer (slice_kind S a) s = s` `m = sourcenode a`
    have "S,slice_kind S \<turnstile> (m#msx',s) =a#asx'\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
      by(fastforce intro:silent_moves_Cons)
    thus "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)" by blast
  qed
qed


lemma silent_moves_intra_path_no_obs:
  assumes "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" and "method_exit m'"
  and "get_proc m = get_proc m'" and "valid_node m" and "length s = length (m#msx')"
  and "\<forall>m \<in> set msx'. return_node m"
  obtains as where "S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
proof(atomize_elim)
  from `method_exit m'` `get_proc m = get_proc m'` `valid_node m`
  obtain as where "m -as\<rightarrow>\<^sub>\<iota>* m'" by(erule intra_path_to_matching_method_exit)
  then obtain x where "distance m m' x" and "x \<le> length as"
    by(erule every_path_distance)
  from `distance m m' x` `m -as\<rightarrow>\<^sub>\<iota>* m'` `obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
    `length s = length (m#msx')` `\<forall>m \<in> set msx'. return_node m`
  show "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
  proof(induct x arbitrary:m as s rule:nat.induct)
    fix m fix s::"(('var \<rightharpoonup> 'val) \<times> 'ret) list"
    assume "distance m m' 0" and "length s = length (m#msx')"
    then obtain as' where "m -as'\<rightarrow>\<^sub>\<iota>* m'" and "length as' = 0"
      by(auto elim:distance.cases)
    hence "m -[]\<rightarrow>\<^sub>\<iota>* m'" by(cases as) auto
    hence [simp]:"m = m'" by(fastforce elim:path.cases simp:intra_path_def)
    with `length s = length (m#msx')`[THEN sym]
    have "S,slice_kind S \<turnstile> (m#msx',s) =[]\<Rightarrow>\<^sub>\<tau> (m#msx',s)" 
      by(fastforce intro:silent_moves_Nil)
    thus "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)" by simp blast
  next
    fix x m as fix s::"(('var \<rightharpoonup> 'val) \<times> 'ret) list"
    assume "distance m m' (Suc x)" and "m -as\<rightarrow>\<^sub>\<iota>* m'"
      and "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
      and "length s = length (m#msx')" and "\<forall>m \<in> set msx'. return_node m"
      and IH:"\<And>m as s. \<lbrakk>distance m m' x; m -as\<rightarrow>\<^sub>\<iota>* m'; 
      obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}; length s = length (m#msx'); 
      \<forall>m \<in> set msx'. return_node m\<rbrakk>
      \<Longrightarrow> \<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
    from `m -as\<rightarrow>\<^sub>\<iota>* m'` have "valid_node m" 
      by(fastforce intro:path_valid_node simp:intra_path_def)
    from `m -as\<rightarrow>\<^sub>\<iota>* m'` have "get_proc m = get_proc m'" by(rule intra_path_get_procs)
    have "m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof
      assume "m \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      with `valid_node m` have "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}"
        by(fastforce intro!:n_in_obs_intra)
      with `obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` show False by simp
    qed
    from `distance m m' (Suc x)` obtain a where "valid_edge a" and "m = sourcenode a"
      and "intra_kind(kind a)" and "distance (targetnode a) m' x"
      and target:"targetnode a = (SOME mx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               distance (targetnode a') m' x \<and>
                                               valid_edge a' \<and> intra_kind (kind a') \<and> 
                                               targetnode a' = mx)"
      by -(erule distance_successor_distance,simp+)
    from `intra_kind(kind a)` `length s = length (m#msx')` `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
      `m = sourcenode a`
    have length:"length (transfer (slice_kind S a) s) = length (targetnode a#msx')"
      by(cases s)
    (auto split:split_if_asm simp add:Let_def slice_kind_def intra_kind_def)
    from `distance (targetnode a) m' x` obtain asx where "targetnode a -asx\<rightarrow>\<^sub>\<iota>* m'" 
      and "length asx = x" and "\<forall>as'. targetnode a -as'\<rightarrow>\<^sub>\<iota>* m' \<longrightarrow> x \<le> length as'"
      by(auto elim:distance.cases)
    from `valid_edge a` `intra_kind(kind a)` `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
      `m = sourcenode a` `obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
    have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
      by(fastforce dest:edge_obs_intra_subset)
    from IH[OF `distance (targetnode a) m' x` `targetnode a -asx\<rightarrow>\<^sub>\<iota>* m'` this
      length `\<forall>m \<in> set msx'. return_node m`] obtain as' 
      where moves:"S,slice_kind S \<turnstile> 
      (targetnode a#msx',transfer (slice_kind S a) s) =as'\<Rightarrow>\<^sub>\<tau> 
      (m'#msx',transfer (slice_kind S a) s)" by blast
    have "pred (slice_kind S a) s \<and> transfer (slice_kind S a) s = s"
    proof(cases "kind a")
      fix f assume "kind a = \<Up>f"
      with `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a` have "slice_kind S a = \<Up>id"
        by(fastforce intro:slice_kind_Upd)
      with `length s = length (m#msx')` show ?thesis by(cases s) auto
    next
      fix Q assume "kind a = (Q)\<^sub>\<surd>"
      with `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a`
        `obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` `distance (targetnode a) m' x`
        `distance m m' (Suc x)` `method_exit m'` `get_proc m = get_proc m'` target
      have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
        by(fastforce intro:slice_kind_Pred_empty_obs_nearer_SOME)
     with `length s = length (m#msx')` show ?thesis by(cases s) auto
    next
      fix Q r p fs assume "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      with `intra_kind(kind a)` have False by(simp add:intra_kind_def)
      thus ?thesis by simp
    next
      fix Q p f assume "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      with `intra_kind(kind a)` have False by(simp add:intra_kind_def)
      thus ?thesis by simp
    qed
    hence "pred (slice_kind S a) s" and "transfer (slice_kind S a) s = s"
      by simp_all
    with `m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a` `valid_edge a`
      `intra_kind(kind a)` `length s = length (m#msx')` `\<forall>m \<in> set msx'. return_node m`
    have "S,slice_kind S \<turnstile> (sourcenode a#msx',s) -a\<rightarrow>\<^sub>\<tau> 
                             (targetnode a#msx',transfer (slice_kind S a) s)"
      by(fastforce intro:silent_move_intra)
    with moves `transfer (slice_kind S a) s = s` `m = sourcenode a`
    have "S,slice_kind S \<turnstile> (m#msx',s) =a#as'\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
      by(fastforce intro:silent_moves_Cons)
    thus "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)" by blast
  qed
qed


lemma silent_moves_vpa_path:
  assumes "S,f \<turnstile> (m#ms,s) =as\<Rightarrow>\<^sub>\<tau> (m'#ms',s')" and "valid_node m"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)" 
  and "ms = targetnodes rs" and "valid_return_list rs m"
  and "length rs = length cs"
  shows "m -as\<rightarrow>* m'" and "valid_path_aux cs as"
proof -
  from assms have "m -as\<rightarrow>* m' \<and> valid_path_aux cs as"
  proof(induct S f "m#ms" s as "m'#ms'" s' arbitrary:m cs ms rs
      rule:silent_moves.induct)
    case (silent_moves_Nil msx sx n\<^sub>c f)
    from `valid_node m'` have "m' -[]\<rightarrow>* m'"
      by (rule empty_path)
    thus ?case by fastforce
  next
    case (silent_moves_Cons S f sx a msx' sx' as s'')
    thus ?case
    proof(induct _ _ "m # ms" _ _ _ _ rule:silent_move.induct)
      case (silent_move_intra f a sx sx' n\<^sub>c msx')
      note IH = `\<And>m cs ms rs. \<lbrakk>msx' = m # ms; valid_node m;
        \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); 
        ms = targetnodes rs; valid_return_list rs m;
        length rs = length cs\<rbrakk>
        \<Longrightarrow> m -as\<rightarrow>* m' \<and> valid_path_aux cs as`
      from `msx' = targetnode a # tl (m # ms)`
      have "msx' = targetnode a # ms" by simp
      from `valid_edge a` `intra_kind (kind a)`
      have "get_proc (sourcenode a) = get_proc (targetnode a)"
        by(rule get_proc_intra)
      with `valid_return_list rs m` `hd (m # ms) = sourcenode a`
      have "valid_return_list rs (targetnode a)"
        apply(clarsimp simp:valid_return_list_def)
        apply(erule_tac x="cs'" in allE) apply clarsimp
        by(case_tac cs') auto
      from `valid_edge a` have "valid_node (targetnode a)" by simp
      from IH[OF `msx' = targetnode a # ms` this 
        `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
        `ms = targetnodes rs` `valid_return_list rs (targetnode a)`
        `length rs = length cs`]
      have "targetnode a -as\<rightarrow>* m'" and "valid_path_aux cs as" by simp_all
      from `valid_edge a` `targetnode a -as\<rightarrow>* m'` 
        `hd (m # ms) = sourcenode a`
      have "m -a#as\<rightarrow>* m'" by(fastforce intro:Cons_path)
      moreover
      from `intra_kind (kind a)` `valid_path_aux cs as`
      have "valid_path_aux cs (a # as)" by(fastforce simp:intra_kind_def)
      ultimately show ?case by simp
    next
      case (silent_move_call f a sx sx' Q r p fs a' n\<^sub>c msx')
      note IH = `\<And>m cs ms rs. \<lbrakk>msx' = m # ms; valid_node m;
        \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); 
        ms = targetnodes rs; valid_return_list rs m;
        length rs = length cs\<rbrakk>
        \<Longrightarrow> m -as\<rightarrow>* m' \<and> valid_path_aux cs as`
      from `valid_edge a` have "valid_node (targetnode a)" by simp
      from `length rs = length cs` 
      have "length (a'#rs) = length (a#cs)" by simp
      from `msx' = targetnode a # targetnode a' # tl (m # ms)`
      have "msx' = targetnode a # targetnode a' # ms" by simp
      from `ms = targetnodes rs` have "targetnode a' # ms = targetnodes (a' # rs)"
        by(simp add:targetnodes_def)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
        by(rule get_proc_call)
      from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
        by(rule get_return_edges_valid)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
      obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      from `valid_edge a` `a' \<in> get_return_edges a`
      have "get_proc (sourcenode a) = get_proc (targetnode a')"
        by(rule get_proc_get_return_edge)
      with `valid_return_list rs m` `hd (m # ms) = sourcenode a`
        `get_proc (targetnode a) = p` `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
      have "valid_return_list (a' # rs) (targetnode a)"
        apply(clarsimp simp:valid_return_list_def)
        apply(case_tac cs') apply auto
        apply(erule_tac x="list" in allE) apply clarsimp
        by(case_tac list)(auto simp:targetnodes_def)
      from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
        `a' \<in> get_return_edges a`
      have "\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)"
        by auto(case_tac i,auto)
      from IH[OF `msx' = targetnode a # targetnode a' # ms` `valid_node (targetnode a)` this 
        `targetnode a' # ms = targetnodes (a' # rs)` 
        `valid_return_list (a' # rs) (targetnode a)` `length (a'#rs) = length (a#cs)`]
      have "targetnode a -as\<rightarrow>* m'" and "valid_path_aux (a # cs) as" by simp_all
      from `valid_edge a` `targetnode a -as\<rightarrow>* m'` 
        `hd (m # ms) = sourcenode a`
      have "m -a#as\<rightarrow>* m'" by(fastforce intro:Cons_path)
      moreover
      from `valid_path_aux (a # cs) as` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "valid_path_aux cs (a # as)" by simp
      ultimately show ?case by simp
    next
      case (silent_move_return f a sx sx' Q p f' n\<^sub>c msx')
      note IH = `\<And>m cs ms rs. \<lbrakk>msx' = m # ms; valid_node m;
        \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); 
        ms = targetnodes rs; valid_return_list rs m;
        length rs = length cs\<rbrakk>
        \<Longrightarrow> m -as\<rightarrow>* m' \<and> valid_path_aux cs as`
      from `valid_edge a` have "valid_node (targetnode a)" by simp
      from `length (m # ms) = length sx` `length sx = Suc (length sx')` 
        `sx' \<noteq> []`
      obtain x xs where "ms = x#xs" by(cases ms) auto
      with `ms = targetnodes rs` obtain r' rs' where "rs = r'#rs'" 
        and "x = targetnode r'" and "xs = targetnodes rs'" 
        by(auto simp:targetnodes_def)
      with `length rs = length cs` obtain c' cs' where "cs = c'#cs'"
        and "length rs' = length cs'"
        by(cases cs) auto
      from `ms = x#xs` `length (m # ms) = length sx` 
        `length sx = Suc (length sx')`
      have "length sx' = Suc (length xs)" by simp
      from `ms = x#xs` `msx' = tl (m # ms)` `hd (tl (m # ms)) = targetnode a`
        `length (m # ms) = length sx` `length sx = Suc (length sx')` `sx' \<noteq> []`
      have "msx' = targetnode a#xs" by simp
      from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
        `rs = r'#rs'` `cs = c'#cs'`
      have "r' \<in> get_return_edges c'" by fastforce
      from `ms = x#xs` `hd (tl (m # ms)) = targetnode a`
      have "x = targetnode a" by simp
      with `valid_return_list rs m` `rs = r'#rs'` `x = targetnode r'`
      have "valid_return_list rs' (targetnode a)"
        apply(clarsimp simp:valid_return_list_def)
        apply(erule_tac x="r'#cs'" in allE) apply clarsimp
        by(case_tac cs')(auto simp:targetnodes_def)
      from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
        `rs = r'#rs'` `cs = c'#cs'`
      have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
        and "r' \<in> get_return_edges c'" by auto
      from IH[OF `msx' = targetnode a#xs` `valid_node (targetnode a)` 
        `\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)` `xs = targetnodes rs'`
        `valid_return_list rs' (targetnode a)` `length rs' = length cs'`]
      have "targetnode a -as\<rightarrow>* m'" and "valid_path_aux cs' as" by simp_all
      from `valid_edge a` `targetnode a -as\<rightarrow>* m'` 
        `hd (m # ms) = sourcenode a`
      have "m -a#as\<rightarrow>* m'" by(fastforce intro:Cons_path)
      moreover
      from `ms = x#xs` `hd (tl (m # ms)) = targetnode a`
      have "x = targetnode a" by simp
      from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
      have "method_exit (sourcenode a)" by(fastforce simp:method_exit_def)
      from `valid_return_list rs m` `hd (m # ms) = sourcenode a` 
        `rs = r'#rs'`
      have "get_proc (sourcenode a) = get_proc (sourcenode r') \<and>
        method_exit (sourcenode r') \<and> valid_edge r'"
        apply(clarsimp simp:valid_return_list_def method_exit_def)
        apply(erule_tac x="[]" in allE) 
        by(auto dest:get_proc_return)
      hence "get_proc (sourcenode a) = get_proc (sourcenode r')"
        and "method_exit (sourcenode r')" and "valid_edge r'" by simp_all
      with `method_exit (sourcenode a)` have "sourcenode r' = sourcenode a"
        by(fastforce intro:method_exit_unique)
      with `valid_edge a` `valid_edge r'` `x = targetnode r'` `x = targetnode a`
      have "r' = a" by(fastforce intro:edge_det)
      with `r' \<in> get_return_edges c'` `valid_path_aux cs' as` `cs = c'#cs'` 
        `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
      have "valid_path_aux cs (a # as)" by simp
      ultimately show ?case by simp
    qed
  qed
  thus "m -as\<rightarrow>* m'" and "valid_path_aux cs as" by simp_all
qed



subsection {* Observable moves *}


inductive observable_move ::
  "'node SDG_node set \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
   (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge \<Rightarrow> 'node list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') -_\<rightarrow> '(_,_')" [51,50,0,0,50,0,0] 51) 
 
  where observable_move_intra:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; intra_kind(kind a); 
    \<forall>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
    hd ms \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; length s' = length s; length ms = length s;
    hd ms = sourcenode a; ms' = (targetnode a)#tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')"

  | observable_move_call:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; 
    valid_edge a'; a' \<in> get_return_edges a;
    \<forall>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
    hd ms \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; length ms = length s; length s' = Suc(length s); 
    hd ms = sourcenode a; ms' = (targetnode a)#(targetnode a')#tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')"

  | observable_move_return:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'; 
    \<forall>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
    length ms = length s; length s = Suc(length s'); s' \<noteq> [];
    hd ms = sourcenode a; hd(tl ms) = targetnode a; ms' = tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')"



inductive observable_moves :: 
  "'node SDG_node set \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
   (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge list \<Rightarrow> 'node list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') =_\<Rightarrow> '(_,_')" [51,50,0,0,50,0,0] 51) 

  where observable_moves_snoc:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s'); S,f \<turnstile> (ms',s') -a\<rightarrow> (ms'',s'')\<rbrakk> 
  \<Longrightarrow> S,f \<turnstile> (ms,s) =as@[a]\<Rightarrow> (ms'',s'')"


lemma observable_move_equal_length:
  assumes "S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')" 
  shows "length ms = length s" and "length ms' = length s'"
proof -
  from `S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')`
  have "length ms = length s \<and> length ms' = length s'"
  proof(induct rule:observable_move.induct)
    case (observable_move_intra f a s s' ms S ms')
    from `pred (f a) s` obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
    from `length ms = length s` `ms' = targetnode a # tl ms`
      `length s' = length s` show ?case by simp
  next
    case (observable_move_call f a s s' Q r p fs a' ms S ms')
    from `pred (f a) s` obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
    from `length ms = length s` `length s' = Suc (length s)` 
      `ms' = targetnode a # targetnode a' # tl ms` show ?case by simp
  next
    case (observable_move_return f a s s' Q p f' ms S ms')
    from `length ms = length s` `length s = Suc (length s')` `ms' = tl ms` `s' \<noteq> []`
    show ?case by simp
  qed
  thus "length ms = length s" and "length ms' = length s'" by simp_all
qed


lemma observable_moves_equal_length:
  assumes "S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')" 
  shows "length ms = length s" and "length ms' = length s'"
  using `S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')`
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc S f ms s as ms' s' a ms'' s'')
  from `S,f \<turnstile> (ms',s') -a\<rightarrow> (ms'',s'')`
  have "length ms' = length s'" "length ms'' = length s''"
    by(rule observable_move_equal_length)+
  moreover
  from `S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')` 
  have "length ms = length s" and "length ms' = length s'"
    by(rule silent_moves_equal_length)+
  ultimately show "length ms = length s" "length ms'' = length s''" by simp_all
qed


lemma observable_move_notempty:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s'); as = []\<rbrakk> \<Longrightarrow> False"
by(induct rule:observable_moves.induct,simp)


lemma silent_move_observable_moves:
  "\<lbrakk>S,f \<turnstile> (ms'',s'') =as\<Rightarrow> (ms',s'); S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms'',s'')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (ms,s) =a#as\<Rightarrow> (ms',s')"
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc S f msx sx as ms' s' a' ms'' s'')
  from `S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (msx,sx)` `S,f \<turnstile> (msx,sx) =as\<Rightarrow>\<^sub>\<tau> (ms',s')`
  have "S,f \<turnstile> (ms,s) =a#as\<Rightarrow>\<^sub>\<tau> (ms',s')" by(fastforce intro:silent_moves_Cons)
  with `S,f \<turnstile> (ms',s') -a'\<rightarrow> (ms'',s'')`
  have "S,f \<turnstile> (ms,s) =(a#as)@[a']\<Rightarrow> (ms'',s'')"
    by(fastforce intro:observable_moves.observable_moves_snoc)
  thus ?case by simp
qed


lemma silent_append_observable_moves:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms'',s''); S,f \<turnstile> (ms'',s'') =as'\<Rightarrow> (ms',s')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (ms,s) =as@as'\<Rightarrow> (ms',s')"
by(induct rule:silent_moves.induct)(auto elim:silent_move_observable_moves)


lemma observable_moves_preds_transfers:
  assumes "S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')"
  shows "preds (map f as) s" and "transfers (map f as) s = s'"
proof -
  from `S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')`
  have "preds (map f as) s \<and> transfers (map f as) s = s'"
  proof(induct rule:observable_moves.induct)
    case (observable_moves_snoc S f ms s as ms' s' a ms'' s'')
    from `S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')` 
    have "preds (map f as) s" and "transfers (map f as) s = s'"
      by(rule silent_moves_preds_transfers)+
    from `S,f \<turnstile> (ms',s') -a\<rightarrow> (ms'',s'')`
    have "pred (f a) s'" and "transfer (f a) s' = s''" 
      by(auto elim:observable_move.cases)
    with `preds (map f as) s` `transfers (map f as) s = s'`
    show ?case by(simp add:preds_split transfers_split)
  qed
  thus "preds (map f as) s" and "transfers (map f as) s = s'" by simp_all
qed


lemma observable_move_vpa_path:
  "\<lbrakk>S,f \<turnstile> (m#ms,s) -a\<rightarrow> (m'#ms',s'); valid_node m; 
    \<forall>i < length rs. rs!i \<in> get_return_edges (cs!i); ms = targetnodes rs;
    valid_return_list rs m; length rs = length cs\<rbrakk> \<Longrightarrow> valid_path_aux cs [a]"
proof(induct S f "m#ms" s a "m'#ms'" s' rule:observable_move.induct)
  case (observable_move_return f a sx sx' Q p f' n\<^sub>c)
  from `length (m # ms) = length sx` `length sx = Suc (length sx')` 
    `sx' \<noteq> []`
  obtain x xs where "ms = x#xs" by(cases ms) auto
  with `ms = targetnodes rs` obtain r' rs' where "rs = r'#rs'" 
    and "x = targetnode r'"     and "xs = targetnodes rs'" 
    by(auto simp:targetnodes_def)
  with `length rs = length cs` obtain c' cs' where "cs = c'#cs'"
    and "length rs' = length cs'"
    by(cases cs) auto
  from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
    `rs = r'#rs'` `cs = c'#cs'`
  have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
    and "r' \<in> get_return_edges c'" by auto
  from `ms = x#xs` `hd (tl (m # ms)) = targetnode a`
  have "x = targetnode a" by simp
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
  have "method_exit (sourcenode a)" by(fastforce simp:method_exit_def)
  from `valid_return_list rs m` `hd (m # ms) = sourcenode a` 
    `rs = r'#rs'`
  have "get_proc (sourcenode a) = get_proc (sourcenode r') \<and>
    method_exit (sourcenode r') \<and> valid_edge r'"
    apply(clarsimp simp:valid_return_list_def method_exit_def)
    apply(erule_tac x="[]" in allE) 
    by(auto dest:get_proc_return)
  hence "get_proc (sourcenode a) = get_proc (sourcenode r')"
    and "method_exit (sourcenode r')" and "valid_edge r'" by simp_all
  with `method_exit (sourcenode a)` have "sourcenode r' = sourcenode a"
    by(fastforce intro:method_exit_unique)
  with `valid_edge a` `valid_edge r'` `x = targetnode r'` `x = targetnode a`
  have "r' = a" by(fastforce intro:edge_det)
  with `r' \<in> get_return_edges c'` `cs = c'#cs'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
  show ?case by simp
qed(auto simp:intra_kind_def)
  


subsection {* Relevant variables *}

inductive_set relevant_vars ::
  "'node SDG_node set \<Rightarrow> 'node SDG_node \<Rightarrow> 'var set" ("rv _")
for S :: "'node SDG_node set" and n :: "'node SDG_node"

where rvI:
  "\<lbrakk>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'; n' \<in> HRB_slice S; V \<in> Use\<^bsub>SDG\<^esub> n';
    \<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''\<rbrakk>
  \<Longrightarrow> V \<in> rv S n"


lemma rvE:
  assumes rv:"V \<in> rv S n"
  obtains as n' where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
  and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
    \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
using rv
by(atomize_elim,auto elim!:relevant_vars.cases)


lemma rv_parent_node:
  "parent_node n = parent_node n' \<Longrightarrow> rv (S::'node SDG_node set) n = rv S n'"
by(fastforce elim:rvE intro:rvI)


lemma obs_intra_empty_rv_empty:
  assumes "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" shows "rv S (CFG_node m) = {}"
proof(rule ccontr)
  assume "rv S (CFG_node m) \<noteq> {}"
  then obtain x where "x \<in> rv S (CFG_node m)" by fastforce
  then obtain n' as where "m -as\<rightarrow>\<^sub>\<iota>* parent_node n'" and "n' \<in> HRB_slice S"
    by(fastforce elim:rvE)
  hence "parent_node n' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(fastforce intro:valid_SDG_node_in_slice_parent_node_in_slice 
                 simp:SDG_to_CFG_set_def)
  with `m -as\<rightarrow>\<^sub>\<iota>* parent_node n'` obtain mx where "mx \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(erule path_ex_obs_intra)
  with `obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` show False by simp
qed


lemma eq_obs_intra_in_rv:
  assumes obs_eq:"obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
                  obs_intra (parent_node n') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "x \<in> rv S n" shows "x \<in> rv S n'"
proof -
  from `x \<in> rv S n` obtain as n''
    where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" and "n'' \<in> HRB_slice S" 
    and "x \<in> Use\<^bsub>SDG\<^esub> n''" 
    and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
      \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> n''"
    by(erule rvE)
  from `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` have "valid_node (parent_node n'')"
    by(fastforce dest:path_valid_node simp:intra_path_def)
  from `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` `n'' \<in> HRB_slice S`
  have "\<exists>nx as' as''. parent_node nx \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> 
                      parent_node n -as'\<rightarrow>\<^sub>\<iota>* parent_node nx \<and>
                      parent_node nx -as''\<rightarrow>\<^sub>\<iota>* parent_node n'' \<and> as = as'@as''"
  proof(cases "\<forall>nx. parent_node nx \<in> set (sourcenodes as) \<longrightarrow> nx \<notin> HRB_slice S")
    case True
    with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` `n'' \<in> HRB_slice S`
    have "parent_node n'' \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce intro:obs_intra_elem valid_SDG_node_in_slice_parent_node_in_slice 
                   simp:SDG_to_CFG_set_def)
    with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` `valid_node (parent_node n'')`
    show ?thesis by(fastforce intro:empty_path simp:intra_path_def)
  next
    case False
    hence "\<exists>nx. parent_node nx \<in> set (sourcenodes as) \<and> nx \<in> HRB_slice S" by simp
    hence "\<exists>mx \<in> set (sourcenodes as). \<exists>nx. mx = parent_node nx \<and> nx \<in> HRB_slice S"
      by fastforce
    then obtain mx ms ms' where "sourcenodes as = ms@mx#ms'"
      and "\<exists>nx. mx = parent_node nx \<and> nx \<in> HRB_slice S"
      and all:"\<forall>x \<in> set ms. \<not> (\<exists>nx. x = parent_node nx \<and> nx \<in> HRB_slice S)"
      by(fastforce elim!:split_list_first_propE)
    then obtain nx' where "mx = parent_node nx'" and "nx' \<in> HRB_slice S" by blast
    from `sourcenodes as = ms@mx#ms'`
    obtain as' a' as'' where "ms = sourcenodes as'"
      and [simp]:"as = as'@a'#as''" and "sourcenode a' = mx"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from all `ms = sourcenodes as'` 
    have "\<forall>nx\<in>set (sourcenodes as'). nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce simp:SDG_to_CFG_set_def)
    from `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` `sourcenode a' = mx`
    have "parent_node n  -as'\<rightarrow>\<^sub>\<iota>* mx" and "valid_edge a'" and "intra_kind(kind a')"
      and "targetnode a' -as''\<rightarrow>\<^sub>\<iota>* parent_node n''"
      by(fastforce dest:path_split simp:intra_path_def)+
    with `sourcenode a' = mx` have "mx -a'#as''\<rightarrow>\<^sub>\<iota>* parent_node n''"
      by(fastforce intro:Cons_path simp:intra_path_def)
    from `parent_node n -as'\<rightarrow>\<^sub>\<iota>* mx` `mx = parent_node nx'` `nx' \<in> HRB_slice S`
      `\<forall>nx\<in>set (sourcenodes as'). nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `ms = sourcenodes as'`
    have "mx \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce intro:obs_intra_elem valid_SDG_node_in_slice_parent_node_in_slice
                   simp:SDG_to_CFG_set_def)
    with `parent_node n -as'\<rightarrow>\<^sub>\<iota>* mx` `mx -a'#as''\<rightarrow>\<^sub>\<iota>* parent_node n''`
      `mx = parent_node nx'`
    show ?thesis by simp blast
  qed
  then obtain nx as' as'' 
    where "parent_node nx \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "parent_node n -as'\<rightarrow>\<^sub>\<iota>* parent_node nx" 
    and "parent_node nx -as''\<rightarrow>\<^sub>\<iota>* parent_node n''" and [simp]:"as = as'@as''"
    by blast
  from `parent_node nx \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` obs_eq
  have "parent_node nx \<in> obs_intra (parent_node n') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by auto
  then obtain asx where "parent_node n' -asx\<rightarrow>\<^sub>\<iota>* parent_node nx" 
    and "\<forall>ni \<in> set(sourcenodes asx). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    and "parent_node nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(erule obs_intraE)
  from `\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
    \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> n''`
  have "\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes as'') 
    \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni"
    by(auto simp:sourcenodes_def)
  from `\<forall>ni \<in> set(sourcenodes asx). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    `parent_node n' -asx\<rightarrow>\<^sub>\<iota>* parent_node nx`
  have "\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes asx) 
    \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni"
  proof(induct asx arbitrary:n')
    case Nil thus ?case by(simp add:sourcenodes_def)
  next
    case (Cons ax' asx')
    note IH = `\<And>n'. \<lbrakk>\<forall>ni\<in>set (sourcenodes asx'). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
      parent_node n' -asx'\<rightarrow>\<^sub>\<iota>* parent_node nx\<rbrakk>
      \<Longrightarrow> \<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes asx') 
              \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni`
    from `parent_node n' -ax'#asx'\<rightarrow>\<^sub>\<iota>* parent_node nx`
    have "parent_node n' -[]@ax'#asx'\<rightarrow>* parent_node nx" 
      and "\<forall>a \<in> set (ax'#asx'). intra_kind(kind a)" by(simp_all add:intra_path_def)
    hence "targetnode ax' -asx'\<rightarrow>* parent_node nx" and "valid_edge ax'"
      and "parent_node n' = sourcenode ax'" by(fastforce dest:path_split)+
    with `\<forall>a \<in> set (ax'#asx'). intra_kind(kind a)`
    have path:"parent_node (CFG_node (targetnode ax')) -asx'\<rightarrow>\<^sub>\<iota>* parent_node nx"
      by(simp add:intra_path_def)
    from `\<forall>ni\<in>set (sourcenodes (ax'#asx')). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have all:"\<forall>ni\<in>set (sourcenodes asx'). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      and "sourcenode ax' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(auto simp:sourcenodes_def)
    from IH[OF all path] 
    have "\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes asx') 
               \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni" .
    with `\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes as'') 
               \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni`
    have all:"\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes (asx'@as'')) 
                   \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni"
      by(auto simp:sourcenodes_def)
    from `parent_node n' -ax'#asx'\<rightarrow>\<^sub>\<iota>* parent_node nx` 
      `parent_node nx -as''\<rightarrow>\<^sub>\<iota>* parent_node n''`
    have path:"parent_node n' -ax'#asx'@as''\<rightarrow>\<^sub>\<iota>* parent_node n''"
      by(fastforce intro:path_Append[of _ "ax'#asx'",simplified] simp:intra_path_def)
    have "\<forall>nx'. parent_node nx' = sourcenode ax' \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> nx'"
    proof
      fix nx' 
      show "parent_node nx' = sourcenode ax' \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> nx'"
      proof
        assume "parent_node nx' = sourcenode ax'"
        show "x \<notin> Def\<^bsub>SDG\<^esub> nx'"
        proof
          assume "x \<in> Def\<^bsub>SDG\<^esub> nx'"
          from `parent_node n' = sourcenode ax'` `parent_node nx' = sourcenode ax'`
          have "parent_node nx' = parent_node n'" by simp
          with `x \<in> Def\<^bsub>SDG\<^esub> nx'` `x \<in> Use\<^bsub>SDG\<^esub> n''` all path
          have "nx' influences x in n''" by(fastforce simp:data_dependence_def)
          hence "nx' s-x\<rightarrow>\<^bsub>dd\<^esub> n''" by(rule sum_SDG_ddep_edge)
          with `n'' \<in> HRB_slice S` have "nx' \<in> HRB_slice S"
            by(fastforce elim:combine_SDG_slices.cases 
                       intro:combine_SDG_slices.intros ddep_slice1 ddep_slice2 
                        simp:HRB_slice_def)
          hence "CFG_node (parent_node nx') \<in> HRB_slice S"
            by(rule valid_SDG_node_in_slice_parent_node_in_slice)
          with `sourcenode ax' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `parent_node n' = sourcenode ax'`
            `parent_node nx' = sourcenode ax'` show False 
            by(simp add:SDG_to_CFG_set_def)
        qed
      qed
    qed
    with all show ?case by(auto simp add:sourcenodes_def)
  qed
  with `\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes as'') 
             \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni`
  have all:"\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes (asx@as'')) 
                 \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni"
    by(auto simp:sourcenodes_def)
  with `parent_node n' -asx\<rightarrow>\<^sub>\<iota>* parent_node nx` 
    `parent_node nx -as''\<rightarrow>\<^sub>\<iota>* parent_node n''`
  have "parent_node n' -asx@as''\<rightarrow>\<^sub>\<iota>* parent_node n''"
    by(fastforce intro:path_Append simp:intra_path_def)
  from this `n'' \<in> HRB_slice S` `x \<in> Use\<^bsub>SDG\<^esub> n''` all
  show "x \<in> rv S n'" by(rule rvI)
qed


lemma closed_eq_obs_eq_rvs:
  fixes S :: "'node SDG_node set"
  assumes obs_eq:"obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
  obs_intra (parent_node n') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "rv S n = rv S n'"
proof
  show "rv S n \<subseteq> rv S n'"
  proof
    fix x assume "x \<in> rv S n"
    with obs_eq show "x \<in> rv S n'" by(rule eq_obs_intra_in_rv)
  qed
next
  show "rv S n' \<subseteq> rv S n"
  proof
    fix x assume "x \<in> rv S n'"
    with obs_eq[THEN sym] show "x \<in> rv S n" by(rule eq_obs_intra_in_rv)
  qed
qed



lemma closed_eq_obs_eq_rvs':
  fixes S :: "'node SDG_node set"
  assumes obs_eq:"obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs_intra m' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "rv S (CFG_node m) = rv S (CFG_node m')"
proof
  show "rv S (CFG_node m) \<subseteq> rv S (CFG_node m')"
  proof
    fix x assume "x \<in> rv S (CFG_node m)"
    with obs_eq show "x \<in> rv S (CFG_node m')" 
      by -(rule eq_obs_intra_in_rv,auto)
  qed
next
  show "rv S (CFG_node m') \<subseteq> rv S (CFG_node m)"
  proof
    fix x assume "x \<in> rv S (CFG_node m')"
    with obs_eq[THEN sym] show "x \<in> rv S (CFG_node m)" 
      by -(rule eq_obs_intra_in_rv,auto)
  qed
qed


lemma rv_branching_edges_slice_kinds_False:
  assumes "valid_edge a" and "valid_edge ax" 
  and "sourcenode a = sourcenode ax" and "targetnode a \<noteq> targetnode ax"
  and "intra_kind (kind a)" and "intra_kind (kind ax)"
  and "preds (slice_kinds S (a#as)) s" 
  and "preds (slice_kinds S (ax#asx)) s'"
  and "length s = length s'" and "snd (hd s) = snd (hd s')"
  and "\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V"
  shows False
proof -
  from `valid_edge a` `valid_edge ax` `sourcenode a = sourcenode ax` 
    `targetnode a \<noteq> targetnode ax` `intra_kind (kind a)` `intra_kind (kind ax)`
  obtain Q Q' where "kind a = (Q)\<^sub>\<surd>" and "kind ax = (Q')\<^sub>\<surd>"
    and "\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  from `valid_edge a` `valid_edge ax` `sourcenode a = sourcenode ax` 
    `targetnode a \<noteq> targetnode ax` `intra_kind (kind a)` `intra_kind (kind ax)`
  obtain P P' where "slice_kind S a = (P)\<^sub>\<surd>" 
    and "slice_kind S ax = (P')\<^sub>\<surd>"
    and "\<forall>s. (P s \<longrightarrow> \<not> P' s) \<and> (P' s \<longrightarrow> \<not> P s)"
    by -(erule slice_deterministic,auto)
  show ?thesis
  proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
    case True
    with `intra_kind (kind a)`
    have "slice_kind S a = kind a" by -(rule slice_intra_kind_in_slice)
    with `preds (slice_kinds S (a#as)) s` `kind a = (Q)\<^sub>\<surd>` 
      `slice_kind S a = (P)\<^sub>\<surd>` have "pred (kind a) s"
      by(simp add:slice_kinds_def)
    from True `sourcenode a = sourcenode ax` `intra_kind (kind ax)`
    have "slice_kind S ax = kind ax" 
      by(fastforce intro:slice_intra_kind_in_slice)
    with `preds (slice_kinds S (ax#asx)) s'` `kind ax = (Q')\<^sub>\<surd>`
      `slice_kind S ax = (P')\<^sub>\<surd>` have "pred (kind ax) s'" 
      by(simp add:slice_kinds_def)
    with `kind ax = (Q')\<^sub>\<surd>` have "Q' (fst (hd s'))" by(cases s') auto
    from `valid_edge a` have "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
      by(fastforce intro:empty_path simp:intra_path_def)
    with True `valid_edge a`
    have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
      by(auto intro!:rvI CFG_Use_SDG_Use simp:sourcenodes_def SDG_to_CFG_set_def)
    with `\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V`
    have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by blast
    with `valid_edge a` `pred (kind a) s` `pred (kind ax) s'` `length s = length s'`
      `snd (hd s) = snd (hd s')`
    have "pred (kind a) s'" by(auto intro:CFG_edge_Uses_pred_equal)
    with `kind a = (Q)\<^sub>\<surd>` have "Q (fst (hd s'))" by(cases s') auto
    with `Q' (fst (hd s'))` `\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)`
    have False by simp
    thus ?thesis by simp
  next
    case False
    with `kind a = (Q)\<^sub>\<surd>` `slice_kind S a = (P)\<^sub>\<surd>` `valid_edge a`
    have "P = (\<lambda>s. False) \<or> P = (\<lambda>s. True)"
      by(fastforce elim:kind_Predicate_notin_slice_slice_kind_Predicate)
    with `slice_kind S a = (P)\<^sub>\<surd>` 
      `preds (slice_kinds S (a#as)) s`
    have "P = (\<lambda>s. True)" by(cases s)(auto simp:slice_kinds_def)
    from `sourcenode a = sourcenode ax` False
    have "sourcenode ax \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with `kind ax = (Q')\<^sub>\<surd>` `slice_kind S ax = (P')\<^sub>\<surd>` `valid_edge ax`
    have "P' = (\<lambda>s. False) \<or> P' = (\<lambda>s. True)"
      by(fastforce elim:kind_Predicate_notin_slice_slice_kind_Predicate)
    with `slice_kind S ax = (P')\<^sub>\<surd>` 
      `preds (slice_kinds S (ax#asx)) s'`
    have "P' = (\<lambda>s. True)" by(cases s')(auto simp:slice_kinds_def)
    with `P = (\<lambda>s. True)` `\<forall>s. (P s \<longrightarrow> \<not> P' s) \<and> (P' s \<longrightarrow> \<not> P s)`
    have False by blast
    thus ?thesis by simp
  qed
qed


lemma rv_edge_slice_kinds:
  assumes "valid_edge a" and "intra_kind (kind a)"
  and "\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V"
  and "preds (slice_kinds S (a#as)) s" and "preds (slice_kinds S (a#asx)) s'"
  shows "\<forall>V\<in>rv S (CFG_node (targetnode a)). 
  state_val (transfer (slice_kind S a) s) V = 
  state_val (transfer (slice_kind S a) s') V"
proof
  fix V assume "V \<in> rv S (CFG_node (targetnode a))"
  from `preds (slice_kinds S (a#as)) s`
  have "s \<noteq> []" by(cases s,auto simp:slice_kinds_def)
  from `preds (slice_kinds S (a#asx)) s'`
  have "s' \<noteq> []" by(cases s',auto simp:slice_kinds_def)
  show "state_val (transfer (slice_kind S a) s) V =
    state_val (transfer (slice_kind S a) s') V"
  proof(cases "V \<in> Def (sourcenode a)")
    case True
    show ?thesis
    proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      with `intra_kind (kind a)` have "slice_kind S a = kind a"
        by -(rule slice_intra_kind_in_slice)
      with `preds (slice_kinds S (a#as)) s` have "pred (kind a) s"
        by(simp add:slice_kinds_def)
      from `slice_kind S a = kind a` 
        `preds (slice_kinds S (a#asx)) s'`
      have "pred (kind a) s'" by(simp add:slice_kinds_def)
      from `valid_edge a` have "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
        by(fastforce intro:empty_path simp:intra_path_def)
      with True `valid_edge a`
      have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
        by(auto intro!:rvI CFG_Use_SDG_Use simp:sourcenodes_def SDG_to_CFG_set_def)
      with `\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V`
      have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by blast
      from `valid_edge a` this `pred (kind a) s` `pred (kind a) s'`
        `intra_kind (kind a)`
      have "\<forall>V \<in> Def (sourcenode a). 
        state_val (transfer (kind a) s) V = state_val (transfer (kind a) s') V"
        by -(rule CFG_intra_edge_transfer_uses_only_Use,auto)
      with `V \<in> Def (sourcenode a)` `slice_kind S a = kind a`
      show ?thesis by simp
    next
      case False
      from `V \<in> rv S (CFG_node (targetnode a))` 
      obtain xs nx where "targetnode a -xs\<rightarrow>\<^sub>\<iota>* parent_node nx"
        and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
        and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes xs) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
      from `valid_edge a` have "valid_node (sourcenode a)" by simp
      from `valid_edge a` `targetnode a -xs\<rightarrow>\<^sub>\<iota>* parent_node nx` `intra_kind (kind a)`
      have "sourcenode a -a#xs \<rightarrow>\<^sub>\<iota>* parent_node nx"
        by(fastforce intro:path.Cons_path simp:intra_path_def)
      with `V \<in> Def (sourcenode a)` `V \<in> Use\<^bsub>SDG\<^esub> nx` `valid_node (sourcenode a)`
        `\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes xs) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''`
      have "(CFG_node (sourcenode a)) influences V in nx"
        by(fastforce intro:CFG_Def_SDG_Def simp:data_dependence_def)
      hence "(CFG_node (sourcenode a)) s-V\<rightarrow>\<^bsub>dd\<^esub> nx" by(rule sum_SDG_ddep_edge)
      from `nx \<in> HRB_slice S` `(CFG_node (sourcenode a)) s-V\<rightarrow>\<^bsub>dd\<^esub> nx`
      have "CFG_node (sourcenode a) \<in> HRB_slice S"
      proof(induct rule:HRB_slice_cases)
        case (phase1 n nx')
        with `(CFG_node (sourcenode a)) s-V\<rightarrow>\<^bsub>dd\<^esub> nx` show ?case
          by(fastforce intro:intro:ddep_slice1 combine_SDG_slices.combSlice_refl 
                       simp:HRB_slice_def)
      next
        case (phase2 nx' n' n'' p n)
        from `(CFG_node (sourcenode a)) s-V\<rightarrow>\<^bsub>dd\<^esub> n` `n \<in> sum_SDG_slice2 n'`
        have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 n'" by(rule ddep_slice2)
        with phase2 show ?thesis
          by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                       simp:HRB_slice_def)
      qed
      with False have False by(simp add:SDG_to_CFG_set_def)
      thus ?thesis by simp
    qed
  next
    case False
    from `V \<in> rv S (CFG_node (targetnode a))` 
    obtain xs nx where "targetnode a -xs\<rightarrow>\<^sub>\<iota>* parent_node nx"
      and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
      and all:"\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes xs) 
                 \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
    from `valid_edge a` have "valid_node (sourcenode a)" by simp
    from `valid_edge a` `targetnode a -xs\<rightarrow>\<^sub>\<iota>* parent_node nx` `intra_kind (kind a)`
    have "sourcenode a -a#xs \<rightarrow>\<^sub>\<iota>* parent_node nx"
      by(fastforce intro:path.Cons_path simp:intra_path_def)
    from False all
    have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (a#xs)) 
                 \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
      by(fastforce dest:SDG_Def_parent_Def simp:sourcenodes_def)
    with `sourcenode a -a#xs \<rightarrow>\<^sub>\<iota>* parent_node nx` `nx \<in> HRB_slice S`
      `V \<in> Use\<^bsub>SDG\<^esub> nx`
    have "V \<in> rv S (CFG_node (sourcenode a))" by(fastforce intro:rvI)
    from `intra_kind (kind a)` show ?thesis
    proof(cases "kind a")
      case(UpdateEdge f)
      show ?thesis
      proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        case True
        with `intra_kind (kind a)` have "slice_kind S a = kind a"
          by(fastforce intro:slice_intra_kind_in_slice)
        from UpdateEdge `s \<noteq> []` have "pred (kind a) s" by(cases s) auto
        with `valid_edge a` `V \<notin> Def (sourcenode a)` `intra_kind (kind a)`
        have "state_val (transfer (kind a) s) V = state_val s V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        from UpdateEdge `s' \<noteq> []` have "pred (kind a) s'" by(cases s') auto
        with `valid_edge a` `V \<notin> Def (sourcenode a)` `intra_kind (kind a)`
        have "state_val (transfer (kind a) s') V = state_val s' V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        with `\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V`
          `state_val (transfer (kind a) s) V = state_val s V`
          `V \<in> rv S (CFG_node (sourcenode a))` `slice_kind S a = kind a`
        show ?thesis by fastforce
      next
        case False
        with UpdateEdge have "slice_kind S a = \<Up>id" 
          by -(rule slice_kind_Upd)
        with `\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V`
          `V \<in> rv S (CFG_node (sourcenode a))` `s \<noteq> []` `s' \<noteq> []`
        show ?thesis by(cases s,auto,cases s',auto)
      qed
    next
      case (PredicateEdge Q)
      show ?thesis
      proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        case True
        with PredicateEdge `intra_kind (kind a)` 
        have "slice_kind S a = (Q)\<^sub>\<surd>"
          by(simp add:slice_intra_kind_in_slice)
        with `\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V`
          `V \<in> rv S (CFG_node (sourcenode a))` `s \<noteq> []` `s' \<noteq> []`
        show ?thesis by(cases s,auto,cases s',auto)
      next
        case False
        with PredicateEdge `valid_edge a` 
        obtain Q' where "slice_kind S a = (Q')\<^sub>\<surd>" 
          by -(erule kind_Predicate_notin_slice_slice_kind_Predicate)
        with`\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V`
          `V \<in> rv S (CFG_node (sourcenode a))` `s \<noteq> []` `s' \<noteq> []`
        show ?thesis by(cases s,auto,cases s',auto)
      qed
    qed (auto simp:intra_kind_def)
  qed
qed



subsection {* The weak simulation relational set @{text WS} *}

inductive_set WS :: "'node SDG_node set \<Rightarrow> (('node list \<times> (('var \<rightharpoonup> 'val) \<times> 'ret) list) \<times> 
  ('node list \<times> (('var \<rightharpoonup> 'val) \<times> 'ret) list)) set"
for S :: "'node SDG_node set"
  where WSI: "\<lbrakk>\<forall>m \<in> set ms. valid_node m; \<forall>m' \<in> set ms'. valid_node m'; 
  length ms = length s; length ms' = length s'; s \<noteq> []; s' \<noteq> []; ms = msx@mx#tl ms';
  get_proc mx = get_proc (hd ms'); 
  \<forall>m \<in> set (tl ms'). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
  msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>);
  \<forall>i < length ms'. snd (s!(length msx + i)) = snd (s'!i);
  \<forall>m \<in> set (tl ms). return_node m;
  \<forall>i < length ms'. \<forall>V \<in> rv S (CFG_node ((mx#tl ms')!i)). 
    (fst (s!(length msx + i))) V = (fst (s'!i)) V;
  obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<rbrakk>
  \<Longrightarrow> ((ms,s),(ms',s')) \<in> WS S"


lemma WS_silent_move:
  assumes "S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1')" and "((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S"
  shows "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>2,s\<^sub>2)) \<in> WS S"
proof -
  from `((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S` obtain msx mx
    where WSE:"\<forall>m \<in> set ms\<^sub>1. valid_node m" "\<forall>m \<in> set ms\<^sub>2. valid_node m"
    "length ms\<^sub>1 = length s\<^sub>1" "length ms\<^sub>2 = length s\<^sub>2" "s\<^sub>1 \<noteq> []" "s\<^sub>2 \<noteq> []" 
    "ms\<^sub>1 = msx@mx#tl ms\<^sub>2" "get_proc mx = get_proc (hd ms\<^sub>2)"
    "\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    "\<forall>m \<in> set (tl ms\<^sub>1). return_node m"
    "\<forall>i < length ms\<^sub>2. snd (s\<^sub>1!(length msx + i)) = snd (s\<^sub>2!i)"
    "\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V"
    "obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(fastforce elim:WS.cases)
  { assume "\<forall>m \<in> set (tl ms\<^sub>1'). return_node m"
    have "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof(cases "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}")
      case True
      with `S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1')` have "obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" 
        by(rule silent_move_empty_obs_slice)
      with `obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
      show ?thesis by simp
    next
      case False
      from this `\<forall>m \<in> set (tl ms\<^sub>1'). return_node m`
      obtain ms' where "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {ms'}"
        by(fastforce dest:obs_singleton_element)
      hence "ms' \<in> obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      from `S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1')` `ms' \<in> obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
        `\<forall>m \<in> set (tl ms\<^sub>1'). return_node m`
      have "ms' \<in> obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(fastforce intro:silent_move_obs_slice)
      from this `\<forall>m \<in> set (tl ms\<^sub>1). return_node m`
      have "obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {ms'}" by(rule obs_singleton_element)
      with `obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {ms'}` 
        `obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      show ?thesis by simp
    qed }
  with `S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1')` WSE
  show ?thesis
  proof(induct S f\<equiv>"kind" ms\<^sub>1 s\<^sub>1 a ms\<^sub>1' s\<^sub>1' rule:silent_move.induct)
    case (silent_move_intra a s\<^sub>1 s\<^sub>1' ms\<^sub>1 S ms\<^sub>1')
    note obs_eq = `\<forall>a\<in>set (tl ms\<^sub>1'). return_node a \<Longrightarrow>
      obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    from `s\<^sub>1 \<noteq> []` `s\<^sub>2 \<noteq> []` obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
    and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from `transfer (kind a) s\<^sub>1 = s\<^sub>1'` `intra_kind (kind a)`
    obtain cf\<^sub>1' where [simp]:"s\<^sub>1' = cf\<^sub>1'#cfs\<^sub>1"
      by(cases cf\<^sub>1,cases "kind a",auto simp:intra_kind_def)
    from `\<forall>m \<in> set ms\<^sub>1. valid_node m` `ms\<^sub>1' = targetnode a # tl ms\<^sub>1` `valid_edge a`
    have "\<forall>m \<in> set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from `length ms\<^sub>1 = length s\<^sub>1` `length s\<^sub>1' = length s\<^sub>1` 
      `ms\<^sub>1' = targetnode a # tl ms\<^sub>1`
    have "length ms\<^sub>1' = length s\<^sub>1'" by(cases ms\<^sub>1) auto
    from `\<forall>m \<in> set (tl ms\<^sub>1). return_node m` `ms\<^sub>1' = targetnode a # tl ms\<^sub>1`
    have "\<forall>m \<in> set (tl ms\<^sub>1'). return_node m" by simp
    from obs_eq[OF this] have "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" .
    from `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` `length ms\<^sub>2 = length s\<^sub>2`
    have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
      by(cases ms\<^sub>2) auto
    show ?case
    proof(cases msx)
      case Nil
      with `ms\<^sub>1 = msx@mx#tl ms\<^sub>2` `hd ms\<^sub>1 = sourcenode a` 
      have [simp]:"mx = sourcenode a" and [simp]:"tl ms\<^sub>1 = tl ms\<^sub>2" by simp_all
      from `\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `(\<exists>m\<in>set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
        hd ms\<^sub>1 \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "hd ms\<^sub>1 \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      with `hd ms\<^sub>1 = sourcenode a` have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from `ms\<^sub>1' = targetnode a # tl ms\<^sub>1` have "ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2"
        by simp
      from `valid_edge a` `intra_kind(kind a)` 
      have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
      with `get_proc mx = get_proc (hd ms\<^sub>2)` 
      have "get_proc (targetnode a) = get_proc (hd ms\<^sub>2)" by simp
      from `transfer (kind a) s\<^sub>1 = s\<^sub>1'` `intra_kind (kind a)`
      have "snd cf\<^sub>1' = snd cf\<^sub>1" by(auto simp:intra_kind_def)
      with `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)` Nil
      have "\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! i) = snd (s\<^sub>2 ! i)"
        by auto(case_tac i,auto)
      have "\<forall>V \<in> rv S (CFG_node (targetnode a)). fst cf\<^sub>1' V = fst cf\<^sub>2 V"
      proof
        fix V assume "V \<in> rv S (CFG_node (targetnode a))"
        from `valid_edge a` `intra_kind (kind a)` `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
          obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          by(rule edge_obs_intra_slice_eq)
        hence "rv S (CFG_node (targetnode a)) = rv S (CFG_node (sourcenode a))" 
          by(rule closed_eq_obs_eq_rvs')
        with `V \<in> rv S (CFG_node (targetnode a))`
        have "V \<in> rv S (CFG_node (sourcenode a))" by simp
        then obtain as n' where "sourcenode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
          and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
          and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
                     \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `valid_edge a`
        have "V \<notin> Def\<^bsub>SDG\<^esub> (CFG_node (sourcenode a))"
          apply(clarsimp simp:intra_path_def)
          apply(erule path.cases)
          by(auto dest:valid_SDG_node_in_slice_parent_node_in_slice 
                  simp:sourcenodes_def SDG_to_CFG_set_def)
        from `valid_edge a` have "valid_node (sourcenode a)" by simp
        with `V \<notin> Def\<^bsub>SDG\<^esub> (CFG_node (sourcenode a))` have "V \<notin> Def (sourcenode a)"
          by(fastforce intro:CFG_Def_SDG_Def valid_SDG_CFG_node)
        with `valid_edge a` `intra_kind (kind a)` `pred (kind a) s\<^sub>1`
        have "state_val (transfer (kind a) s\<^sub>1) V = state_val s\<^sub>1 V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        with `transfer (kind a) s\<^sub>1 = s\<^sub>1'` have "fst cf\<^sub>1' V = fst cf\<^sub>1 V" by simp
        from `V \<in> rv S (CFG_node (sourcenode a))` `msx = []`
          `\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V`
        have "fst cf\<^sub>1 V = fst cf\<^sub>2 V" by simp
        with `fst cf\<^sub>1' V = fst cf\<^sub>1 V` show "fst cf\<^sub>1' V = fst cf\<^sub>2 V" by simp
      qed
      with `\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2) ! i)).
        (fst (s\<^sub>1 ! (length msx + i))) V = (fst (s\<^sub>2 ! i)) V` Nil
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((targetnode a # tl ms\<^sub>2) ! i)).
        (fst (s\<^sub>1' ! (length [] + i))) V = (fst (s\<^sub>2 ! i)) V"
        by auto (case_tac i,auto)
      with `\<forall>m \<in> set ms\<^sub>1'. valid_node m` `\<forall>m \<in> set ms\<^sub>2. valid_node m`
        `length ms\<^sub>1' = length s\<^sub>1'` `length ms\<^sub>2 = length s\<^sub>2`
        `ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2` 
        `get_proc (targetnode a) = get_proc (hd ms\<^sub>2)`
        `\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `\<forall>m \<in> set (tl ms\<^sub>1). return_node m`
        `obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! i) = snd (s\<^sub>2 ! i)`
      show ?thesis by(auto intro!:WSI)
    next
      case (Cons mx' msx')
      with `ms\<^sub>1 = msx@mx#tl ms\<^sub>2` `hd ms\<^sub>1 = sourcenode a`
      have [simp]:"mx' = sourcenode a" and [simp]:"tl ms\<^sub>1 = msx'@mx#tl ms\<^sub>2" 
        by simp_all
     from `ms\<^sub>1' = targetnode a # tl ms\<^sub>1` have "ms\<^sub>1' = ((targetnode a)#msx')@mx#tl ms\<^sub>2"
        by simp
      from `\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V` Cons
      have rv:"\<forall>V\<in>rv S (CFG_node mx).
        (fst (s\<^sub>1' ! length (targetnode a#msx'))) V = state_val s\<^sub>2 V" by fastforce
      from `ms\<^sub>1 = msx@mx#tl ms\<^sub>2` Cons `ms\<^sub>1' = targetnode a # tl ms\<^sub>1`
      have "ms\<^sub>1' = ((targetnode a)#msx')@mx#tl ms\<^sub>2" by simp
      from `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)` Cons
      have "\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length msx + i)) = snd (s\<^sub>2 ! i)" by fastforce 
      from `\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V` Cons
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1' ! length msx)) V = state_val s\<^sub>2 V"
        by simp
      with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` Cons
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2)!i)).
             (fst (s\<^sub>1'!(length (targetnode a # msx') + i))) V = (fst (s\<^sub>2!i)) V"
        by clarsimp
      with `\<forall>m\<in>set ms\<^sub>1'. valid_node m` `\<forall>m\<in>set ms\<^sub>2. valid_node m`
        `length ms\<^sub>1' = length s\<^sub>1'` `length ms\<^sub>2 = length s\<^sub>2` 
        `ms\<^sub>1' = ((targetnode a)#msx')@mx#tl ms\<^sub>2`
        `\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `\<forall>m \<in> set (tl ms\<^sub>1'). return_node m` `get_proc mx = get_proc (hd ms\<^sub>2)`
        `msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
        `obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` Cons
        `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length msx + i)) = snd (s\<^sub>2 ! i)`
      show ?thesis by -(rule WSI,clarsimp+,fastforce,clarsimp+)
    qed
  next
    case (silent_move_call a s\<^sub>1 s\<^sub>1' Q r p fs a' ms\<^sub>1 S ms\<^sub>1')
    note obs_eq = `\<forall>a\<in>set (tl ms\<^sub>1'). return_node a \<Longrightarrow>
      obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    from `s\<^sub>1 \<noteq> []` `s\<^sub>2 \<noteq> []` obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
      and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
    obtain ins outs where "(p,ins,outs) \<in> set procs"
      by(fastforce dest!:callee_in_procs)
    with `transfer (kind a) s\<^sub>1 = s\<^sub>1'` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have [simp]:"s\<^sub>1' = (Map.empty(ins [:=] params fs (fst cf\<^sub>1)), r) # cf\<^sub>1 # cfs\<^sub>1"
      by simp(unfold formal_in_THE,simp)
    from `length ms\<^sub>1 = length s\<^sub>1` `ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1`
    have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
      by(rule get_return_edges_valid)
    with `\<forall>m\<in>set ms\<^sub>1. valid_node m` `valid_edge a` 
      `ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1`
    have "\<forall>m\<in>set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from `valid_edge a'` `valid_edge a` `a' \<in> get_return_edges a`
    have "return_node (targetnode a')" by(fastforce simp:return_node_def)
    with `valid_edge a` `a' \<in> get_return_edges a` `valid_edge a'`
    have "call_of_return_node (targetnode a') (sourcenode a)"
      by(simp add:call_of_return_node_def) blast
    from `\<forall>m \<in> set (tl ms\<^sub>1). return_node m` `return_node (targetnode a')`
      `ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1`
    have "\<forall>m \<in> set (tl ms\<^sub>1'). return_node m" by simp
    from obs_eq[OF this] have "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" .
    from `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` `length ms\<^sub>2 = length s\<^sub>2`
    have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
      by(erule_tac x="0" in allE) auto
    show ?case
    proof(cases msx)
      case Nil
      with `ms\<^sub>1 = msx@mx#tl ms\<^sub>2` `hd ms\<^sub>1 = sourcenode a` 
      have [simp]:"mx = sourcenode a" and [simp]:"tl ms\<^sub>1 = tl ms\<^sub>2" by simp_all
      from `\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `(\<exists>m\<in>set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
        hd ms\<^sub>1 \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "hd ms\<^sub>1 \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      with `hd ms\<^sub>1 = sourcenode a` have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from `valid_edge a` `a' \<in> get_return_edges a`
      obtain a'' where "valid_edge a''" and "sourcenode a'' = sourcenode a"
        and "targetnode a'' = targetnode a'" and "intra_kind(kind a'')"
        by -(drule call_return_node_edge,auto simp:intra_kind_def)
      from `valid_edge a''` `intra_kind(kind a'')`
      have "get_proc (sourcenode a'') = get_proc (targetnode a'')"
        by(rule get_proc_intra)
      with `sourcenode a'' = sourcenode a` `targetnode a'' = targetnode a'`
        `get_proc mx = get_proc (hd ms\<^sub>2)` 
      have "get_proc (targetnode a') = get_proc (hd ms\<^sub>2)" by simp
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
      have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')"
        by(fastforce intro:sum_SDG_call_summary_edge)
      have "targetnode a' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      proof
        assume "targetnode a' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        hence "CFG_node (targetnode a') \<in> HRB_slice S" by(simp add:SDG_to_CFG_set_def)
        hence "CFG_node (sourcenode a) \<in> HRB_slice S"
        proof(induct "CFG_node (targetnode a')" rule:HRB_slice_cases)
          case (phase1 nx)
          with `CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')`
          show ?case by(fastforce intro:combine_SDG_slices.combSlice_refl sum_slice1
                                  simp:HRB_slice_def)
        next
          case (phase2 nx n' n'' p')
          from `CFG_node (targetnode a') \<in> sum_SDG_slice2 n'` 
            `CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')` `valid_edge a`
          have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 n'"
            by(fastforce intro:sum_slice2)
          with `n' \<in> sum_SDG_slice1 nx` `n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')` 
            `nx \<in> S`
          show ?case
            by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                         simp:HRB_slice_def)
        qed
        with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` show False
          by(simp add:SDG_to_CFG_set_def HRB_slice_def)
      qed
      from `ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1`
      have "ms\<^sub>1' = [targetnode a] @ targetnode a' # tl ms\<^sub>2" by simp
      from `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)` Nil
      have "\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length [targetnode a] + i)) = snd (s\<^sub>2 ! i)"
        by fastforce
      have "\<forall>V\<in>rv S (CFG_node (targetnode a')). (fst (s\<^sub>1' ! 1)) V = state_val s\<^sub>2 V"
      proof
        fix V assume "V \<in> rv S (CFG_node (targetnode a'))"
        from `valid_edge a` `a' \<in> get_return_edges a`
        obtain a'' where edge:"valid_edge a''" "sourcenode a'' = sourcenode a"
          "targetnode a'' = targetnode a'" "intra_kind(kind a'')"
          by -(drule call_return_node_edge,auto simp:intra_kind_def)
        from `V \<in> rv S (CFG_node (targetnode a'))`
        obtain as n' where "targetnode a' -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
          and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        from `targetnode a' -as\<rightarrow>\<^sub>\<iota>* parent_node n'` edge
        have "sourcenode a -a''#as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          by(fastforce intro:Cons_path simp:intra_path_def)
        from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        have "V \<notin> Def (sourcenode a)"
          by(fastforce dest:call_source_Def_empty)
        with `\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''` `sourcenode a'' = sourcenode a`
        have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (a''#as)) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce dest:SDG_Def_parent_Def simp:sourcenodes_def)
        with `sourcenode a -a''#as\<rightarrow>\<^sub>\<iota>* parent_node n'` `n' \<in> HRB_slice S` 
          `V \<in> Use\<^bsub>SDG\<^esub> n'`
        have "V \<in> rv S (CFG_node (sourcenode a))" by(fastforce intro:rvI)
        from `\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V` Nil
        have "\<forall>V\<in>rv S (CFG_node (sourcenode a)). fst cf\<^sub>1 V = fst cf\<^sub>2 V" by simp
        with `V \<in> rv S (CFG_node (sourcenode a))` have "fst cf\<^sub>1 V = fst cf\<^sub>2 V" by simp
        thus "(fst (s\<^sub>1' ! 1)) V = state_val s\<^sub>2 V" by simp
      qed
      with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` Nil
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((targetnode a' # tl ms\<^sub>2)!i)).
        (fst (s\<^sub>1'!(length [targetnode a] + i))) V = (fst (s\<^sub>2!i)) V"
        by clarsimp(case_tac i,auto)
      with `\<forall>m\<in>set ms\<^sub>1'. valid_node m` `\<forall>m\<in>set ms\<^sub>2. valid_node m`
        `length ms\<^sub>1' = length s\<^sub>1'` `length ms\<^sub>2 = length s\<^sub>2`
        `\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `ms\<^sub>1' = [targetnode a] @ targetnode a' # tl ms\<^sub>2`
        `targetnode a' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `return_node (targetnode a')`
        `obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `get_proc (targetnode a') = get_proc (hd ms\<^sub>2)`
        `\<forall>m \<in> set (tl ms\<^sub>1'). return_node m` `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `call_of_return_node (targetnode a') (sourcenode a)`
        `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length [targetnode a] + i)) = snd (s\<^sub>2 ! i)`
      show ?thesis by(auto intro!:WSI)
    next
      case (Cons mx' msx')
      with `ms\<^sub>1 = msx@mx#tl ms\<^sub>2` `hd ms\<^sub>1 = sourcenode a`
      have [simp]:"mx' = sourcenode a" and [simp]:"tl ms\<^sub>1 = msx'@mx#tl ms\<^sub>2" 
        by simp_all
      from `ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1` 
      have "ms\<^sub>1' = (targetnode a # targetnode a' # msx')@mx#tl ms\<^sub>2"
        by simp
      from `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)` Cons
      have "\<forall>i<length ms\<^sub>2.
        snd (s\<^sub>1' ! (length (targetnode a # targetnode a' # msx') + i)) = snd (s\<^sub>2 ! i)"
        by fastforce
      from `\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V` Cons
      have "\<forall>V\<in>rv S (CFG_node mx). 
        (fst (s\<^sub>1' ! length(targetnode a # targetnode a' # msx'))) V = state_val s\<^sub>2 V" 
        by simp
      with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` Cons
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2)!i)).
        (fst (s\<^sub>1'!(length (targetnode a # targetnode a' # msx') + i))) V = 
        (fst (s\<^sub>2!i)) V"
        by clarsimp
      with `\<forall>m\<in>set ms\<^sub>1'. valid_node m` `\<forall>m\<in>set ms\<^sub>2. valid_node m`
        `length ms\<^sub>1' = length s\<^sub>1'` `length ms\<^sub>2 = length s\<^sub>2` 
        `ms\<^sub>1' = (targetnode a # targetnode a' # msx')@mx#tl ms\<^sub>2`
        `return_node (targetnode a')`
        `\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
        `obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` Cons
        `get_proc mx = get_proc (hd ms\<^sub>2)` `\<forall>m \<in> set (tl ms\<^sub>1'). return_node m`
        `\<forall>i<length ms\<^sub>2.
        snd (s\<^sub>1' ! (length (targetnode a # targetnode a' # msx') + i)) = snd (s\<^sub>2 ! i)`
      show ?thesis by -(rule WSI,clarsimp+,fastforce,clarsimp+)
    qed
  next
    case (silent_move_return a s\<^sub>1 s\<^sub>1' Q p f' ms\<^sub>1 S ms\<^sub>1')
    note obs_eq = `\<forall>a\<in>set (tl ms\<^sub>1'). return_node a \<Longrightarrow>
      obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    from `transfer (kind a) s\<^sub>1 = s\<^sub>1'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `s\<^sub>1 \<noteq> []` `s\<^sub>1' \<noteq> []`
    obtain cf\<^sub>1 cfx\<^sub>1 cfs\<^sub>1 cf\<^sub>1' where [simp]:"s\<^sub>1 = cf\<^sub>1#cfx\<^sub>1#cfs\<^sub>1"
      and "s\<^sub>1' = (f' (fst cf\<^sub>1) (fst cfx\<^sub>1),snd cfx\<^sub>1)#cfs\<^sub>1"
      by(cases s\<^sub>1,auto,case_tac list,fastforce+)
    from `s\<^sub>2 \<noteq> []` obtain cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>2) auto
    from `length ms\<^sub>1 = length s\<^sub>1` have "ms\<^sub>1 \<noteq> []" and "tl ms\<^sub>1 \<noteq> []" by(cases ms\<^sub>1,auto)+
    from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
    obtain a' Q' r' fs' where "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
      and "a \<in> get_return_edges a'"
      by -(drule return_needs_call,auto)
    then obtain ins outs where "(p,ins,outs) \<in> set procs"
      by(fastforce dest!:callee_in_procs)
    with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
    have "f' (fst cf\<^sub>1) (fst cfx\<^sub>1) = 
      (fst cfx\<^sub>1)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs)"
      by(rule CFG_return_edge_fun)
    with `s\<^sub>1' = (f' (fst cf\<^sub>1) (fst cfx\<^sub>1),snd cfx\<^sub>1)#cfs\<^sub>1`
    have [simp]:"s\<^sub>1' = ((fst cfx\<^sub>1)
      (ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs),snd cfx\<^sub>1)#cfs\<^sub>1" by simp
    from `\<forall>m\<in>set ms\<^sub>1. valid_node m` `ms\<^sub>1' = tl ms\<^sub>1` have "\<forall>m\<in>set ms\<^sub>1'. valid_node m"
      by(cases ms\<^sub>1) auto
    from `length ms\<^sub>1 = length s\<^sub>1` `ms\<^sub>1' = tl ms\<^sub>1`
    have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from `\<forall>m\<in>set (tl ms\<^sub>1). return_node m` `ms\<^sub>1' = tl ms\<^sub>1` `ms\<^sub>1 \<noteq> []` `tl ms\<^sub>1 \<noteq> []`
    have "\<forall>m\<in>set (tl ms\<^sub>1'). return_node m" by(cases ms\<^sub>1)(auto,cases ms\<^sub>1',auto)
    from obs_eq[OF this] have "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" .
    show ?case
    proof(cases msx)
      case Nil
      with `ms\<^sub>1 = msx@mx#tl ms\<^sub>2` `hd ms\<^sub>1 = sourcenode a` 
      have "mx = sourcenode a" and "tl ms\<^sub>1 = tl ms\<^sub>2" by simp_all
      with `\<exists>m\<in>set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have False by fastforce
      thus ?thesis by simp
    next
      case (Cons mx' msx')
      with `ms\<^sub>1 = msx@mx#tl ms\<^sub>2` `hd ms\<^sub>1 = sourcenode a`
      have [simp]:"mx' = sourcenode a" and [simp]:"tl ms\<^sub>1 = msx'@mx#tl ms\<^sub>2"
        by simp_all
      from `ms\<^sub>1' = tl ms\<^sub>1` have "ms\<^sub>1' = msx'@mx#tl ms\<^sub>2" by simp
      with `ms\<^sub>1 = msx@mx#tl ms\<^sub>2` `\<forall>m\<in>set (tl ms\<^sub>1). return_node m` Cons
      have "\<forall>m\<in>set (tl ms\<^sub>1'). return_node m"
        by(cases msx') auto
      from `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)` Cons
      have "\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length msx' + i)) = snd (s\<^sub>2 ! i)"
        by auto(case_tac i,auto,cases msx',auto)
      from `\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2) ! i)).
        (fst (s\<^sub>1 ! (length msx + i))) V = (fst (s\<^sub>2 ! i)) V`
        `length ms\<^sub>2 = length s\<^sub>2` `s\<^sub>2 \<noteq> []`
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
        by fastforce
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1' ! length msx')) V = state_val s\<^sub>2 V"
      proof(cases msx')
        case Nil
        with `\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V`
          `msx = mx'#msx'`
        have rv:"\<forall>V\<in>rv S (CFG_node mx). fst cfx\<^sub>1 V = fst cf\<^sub>2 V" by fastforce
        from Nil `tl ms\<^sub>1 = msx'@mx#tl ms\<^sub>2` `hd (tl ms\<^sub>1) = targetnode a`
        have [simp]:"mx = targetnode a" by simp
        from Cons 
          `msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
        obtain mx'' where "call_of_return_node mx mx''" and "mx'' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          by blast
        hence "mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
          by(rule call_node_notin_slice_return_node_neither)
        have "\<forall>V\<in>rv S (CFG_node mx). 
          (fst cfx\<^sub>1)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = fst cf\<^sub>2 V"
        proof
          fix V assume "V\<in>rv S (CFG_node mx)"
          show "(fst cfx\<^sub>1)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = 
            fst cf\<^sub>2 V"
          proof(cases "V \<in> set (ParamDefs (targetnode a))")
            case True
            with `valid_edge a` have "V \<in> Def (targetnode a)"
              by(fastforce intro:ParamDefs_in_Def)
            with `valid_edge a` have "V \<in> Def\<^bsub>SDG\<^esub> (CFG_node (targetnode a))"
              by(auto intro!:CFG_Def_SDG_Def)
            from `V\<in>rv S (CFG_node mx)` obtain as n' 
              where "targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
              and "n' \<in> HRB_slice S" "V \<in> Use\<^bsub>SDG\<^esub> n'"
              and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
              \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
            from `targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'` `n' \<in> HRB_slice S`
              `mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
            obtain ax asx where "as = ax#asx"
              by(auto simp:intra_path_def)(erule path.cases,
                 auto dest:valid_SDG_node_in_slice_parent_node_in_slice 
                      simp:SDG_to_CFG_set_def)
            with `targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'` 
            have "targetnode a = sourcenode ax" and "valid_edge ax"
              by(auto elim:path.cases simp:intra_path_def)
            with `\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
              \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''` `as = ax#asx` `V \<in> Def\<^bsub>SDG\<^esub> (CFG_node (targetnode a))`
            have False by(fastforce simp:sourcenodes_def)
            thus ?thesis by simp
          next
            case False
            with `V\<in>rv S (CFG_node mx)` rv show ?thesis
              by(fastforce dest:fun_upds_notin[of  _ _ "fst cfx\<^sub>1"])
          qed
        qed
        with Nil `msx = mx'#msx'` show ?thesis by fastforce
      next
        case Cons
        with `\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V`
          `msx = mx'#msx'`
        show ?thesis by fastforce
      qed
      with `\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V` Cons
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1' ! length msx')) V = state_val s\<^sub>2 V"
        by(cases msx') auto
      with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` Cons
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2) ! i)).
        (fst (s\<^sub>1' ! (length msx' + i))) V = (fst (s\<^sub>2 ! i)) V"
        by clarsimp(case_tac i,auto)
      with `\<forall>m\<in>set ms\<^sub>1'. valid_node m` `\<forall>m\<in>set ms\<^sub>2. valid_node m`
        `length ms\<^sub>1' = length s\<^sub>1'` `length ms\<^sub>2 = length s\<^sub>2` 
        `ms\<^sub>1' = msx'@mx#tl ms\<^sub>2` `get_proc mx = get_proc (hd ms\<^sub>2)`
        `\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
        `\<forall>m\<in>set (tl ms\<^sub>1'). return_node m` Cons `get_proc mx = get_proc (hd ms\<^sub>2)`
        `\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length msx' + i)) = snd (s\<^sub>2 ! i)`
       show ?thesis by(auto intro!:WSI)
    qed
  qed
qed


lemma WS_silent_moves:
  "\<lbrakk>S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1'); ((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S\<rbrakk>
  \<Longrightarrow> ((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>2,s\<^sub>2)) \<in> WS S"
by(induct S f\<equiv>"kind" ms\<^sub>1 s\<^sub>1 as ms\<^sub>1' s\<^sub>1' rule:silent_moves.induct,
  auto dest:WS_silent_move)


lemma WS_observable_move:
  assumes "((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S"
  and "S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow> (ms\<^sub>1',s\<^sub>1')" and "s\<^sub>1' \<noteq> []"
  obtains as where "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
  and "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
proof(atomize_elim)
  from `((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S` obtain msx mx
    where assms:"\<forall>m \<in> set ms\<^sub>1. valid_node m" "\<forall>m \<in> set ms\<^sub>2. valid_node m"
    "length ms\<^sub>1 = length s\<^sub>1" "length ms\<^sub>2 = length s\<^sub>2" "s\<^sub>1 \<noteq> []" "s\<^sub>2 \<noteq> []" 
    "ms\<^sub>1 = msx@mx#tl ms\<^sub>2" "get_proc mx = get_proc (hd ms\<^sub>2)" 
    "\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    "\<forall>m \<in> set (tl ms\<^sub>1). return_node m"
    "\<forall>i < length ms\<^sub>2. snd (s\<^sub>1!(length msx + i)) = snd (s\<^sub>2!i)"
    "\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V"
    "obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(fastforce elim:WS.cases)
  from `S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow> (ms\<^sub>1',s\<^sub>1')` assms
  show "\<exists>as. ((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S \<and>
    S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as @ [a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
  proof(induct S f\<equiv>"kind" ms\<^sub>1 s\<^sub>1 a ms\<^sub>1' s\<^sub>1' rule:observable_move.induct)
    case (observable_move_intra a s\<^sub>1 s\<^sub>1' ms\<^sub>1 S ms\<^sub>1')
    from `s\<^sub>1 \<noteq> []` `s\<^sub>2 \<noteq> []` obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
      and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from `length ms\<^sub>1 = length s\<^sub>1` `s\<^sub>1 \<noteq> []` have [simp]:"ms\<^sub>1 \<noteq> []" by(cases ms\<^sub>1) auto
    from `length ms\<^sub>2 = length s\<^sub>2` `s\<^sub>2 \<noteq> []` have [simp]:"ms\<^sub>2 \<noteq> []" by(cases ms\<^sub>2) auto
    from `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `hd ms\<^sub>1 = sourcenode a` `ms\<^sub>1 = msx@mx#tl ms\<^sub>2`
      `msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
    have [simp]:"mx = sourcenode a" "msx = []" and [simp]:"tl ms\<^sub>2 = tl ms\<^sub>1"
      by(cases msx,auto)+
    hence "length ms\<^sub>1 = length ms\<^sub>2" by(cases ms\<^sub>2) auto
    with `length ms\<^sub>1 = length s\<^sub>1` `length ms\<^sub>2 = length s\<^sub>2`
    have "length s\<^sub>1 = length s\<^sub>2" by simp
    from `hd ms\<^sub>1 \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `hd ms\<^sub>1 = sourcenode a`
    have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with `valid_edge a`
    have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
      by(fastforce intro!:n_in_obs_intra)
    from `\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}` 
      `hd ms\<^sub>1 = sourcenode a` 
    have "(hd ms\<^sub>1#tl ms\<^sub>1) \<in> obs ([]@hd ms\<^sub>1#tl ms\<^sub>1) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(cases ms\<^sub>1)(auto intro!:obsI)
    hence "ms\<^sub>1 \<in> obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with `obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    from `ms\<^sub>2 \<noteq> []` `length ms\<^sub>2 = length s\<^sub>2` have "length s\<^sub>2 = length (hd ms\<^sub>2#tl ms\<^sub>2)"
      by(fastforce dest!:hd_Cons_tl)
    from `\<forall>m \<in> set (tl ms\<^sub>1). return_node m` have "\<forall>m \<in> set (tl ms\<^sub>2). return_node m"
      by simp
    with `ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "hd ms\<^sub>1 \<in> obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof(rule obsE)
      fix nsx n nsx' n'
      assume "ms\<^sub>2 = nsx @ n # nsx'" and "ms\<^sub>1 = n' # nsx'"
        and "n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      from `ms\<^sub>2 = nsx @ n # nsx'` `ms\<^sub>1 = n' # nsx'` `tl ms\<^sub>2 = tl ms\<^sub>1`
      have [simp]:"nsx = []" by(cases nsx) auto
      with `ms\<^sub>2 = nsx @ n # nsx'` have [simp]:"n = hd ms\<^sub>2" by simp
      from `ms\<^sub>1 = n' # nsx'` have [simp]:"n' = hd ms\<^sub>1" by simp
      with `n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` show ?thesis by simp
    qed
    with `length s\<^sub>2 = length (hd ms\<^sub>2#tl ms\<^sub>2)` `\<forall>m \<in> set (tl ms\<^sub>2). return_node m`
    obtain as where "S,slice_kind S \<turnstile> (hd ms\<^sub>2#tl ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (hd ms\<^sub>1#tl ms\<^sub>1,s\<^sub>2)"
      by(fastforce elim:silent_moves_intra_path_obs[of _ _ _ s\<^sub>2 "tl ms\<^sub>2"])
    with `ms\<^sub>2 \<noteq> []` have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
      by(fastforce dest!:hd_Cons_tl)
    from `valid_edge a` have "valid_node (sourcenode a)" by simp
    hence "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
      by(fastforce intro:empty_path simp:intra_path_def)
    with `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "\<forall>V. V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a)) 
      \<longrightarrow> V \<in> rv S (CFG_node (sourcenode a))"
      by auto(rule rvI,auto simp:SDG_to_CFG_set_def sourcenodes_def)
    with `valid_node (sourcenode a)`
    have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
      by(fastforce intro:CFG_Use_SDG_Use)
    from `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` `length ms\<^sub>2 = length s\<^sub>2`
    have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
      by(cases ms\<^sub>2) auto
    with `\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))`
    have "\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V" by fastforce
    moreover
    from `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)`
    have "snd (hd s\<^sub>1) = snd (hd s\<^sub>2)" by(erule_tac x="0" in allE) auto
    ultimately have "pred (kind a) s\<^sub>2"
      using `valid_edge a` `pred (kind a) s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2`
      by(fastforce intro:CFG_edge_Uses_pred_equal)
    from `ms\<^sub>1' = targetnode a # tl ms\<^sub>1` `length s\<^sub>1' = length s\<^sub>1` 
      `length ms\<^sub>1 = length s\<^sub>1` have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from `transfer (kind a) s\<^sub>1 = s\<^sub>1'` `intra_kind (kind a)`
    obtain cf\<^sub>1' where [simp]:"s\<^sub>1' = cf\<^sub>1'#cfs\<^sub>1"
      by(cases cf\<^sub>1,cases "kind a",auto simp:intra_kind_def)
    from `intra_kind (kind a)` `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `pred (kind a) s\<^sub>2`
    have "pred (slice_kind S a) s\<^sub>2" by(simp add:slice_intra_kind_in_slice)
    from `valid_edge a` `length s\<^sub>1 = length s\<^sub>2` `transfer (kind a) s\<^sub>1 = s\<^sub>1'`
    have "length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)"
      by(fastforce intro:length_transfer_kind_slice_kind)
    with `length s\<^sub>1 = length s\<^sub>2`
    have "length s\<^sub>2 = length (transfer (slice_kind S a) s\<^sub>2)" by simp
    with `pred (slice_kind S a) s\<^sub>2` `valid_edge a` `intra_kind (kind a)`
      `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `hd ms\<^sub>1 \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `hd ms\<^sub>1 = sourcenode a`
      `length ms\<^sub>1 = length s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2`
      `ms\<^sub>1' = targetnode a # tl ms\<^sub>1` `\<forall>m \<in> set (tl ms\<^sub>2). return_node m`
    have "S,slice_kind S \<turnstile> (ms\<^sub>1,s\<^sub>2) -a\<rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(auto intro:observable_move.observable_move_intra)
    with `S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)` 
    have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(rule observable_moves_snoc)
    from `\<forall>m \<in> set ms\<^sub>1. valid_node m` `ms\<^sub>1' = targetnode a # tl ms\<^sub>1` `valid_edge a`
    have "\<forall>m \<in> set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from `\<forall>m \<in> set (tl ms\<^sub>2). return_node m` `ms\<^sub>1' = targetnode a # tl ms\<^sub>1`
      `ms\<^sub>1' = targetnode a # tl ms\<^sub>1`
    have "\<forall>m \<in> set (tl ms\<^sub>1'). return_node m" by fastforce
    from `ms\<^sub>1' = targetnode a # tl ms\<^sub>1` `tl ms\<^sub>2 = tl ms\<^sub>1`
    have "ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2" by simp
    from `intra_kind (kind a)` `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have cf2':"\<exists>cf\<^sub>2'. transfer (slice_kind S a) s\<^sub>2 = cf\<^sub>2'#cfs\<^sub>2 \<and> snd cf\<^sub>2' = snd cf\<^sub>2"
      by(cases cf\<^sub>2)(auto dest:slice_intra_kind_in_slice simp:intra_kind_def)
    from `transfer (kind a) s\<^sub>1 = s\<^sub>1'` `intra_kind (kind a)`
    have "snd cf\<^sub>1' = snd cf\<^sub>1" by(auto simp:intra_kind_def)
    with `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)`
      `snd (hd s\<^sub>1) = snd (hd s\<^sub>2)` `ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2`
      cf2' `length ms\<^sub>1 = length ms\<^sub>2`
    have "\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)"
      by auto(case_tac i,auto)
    have "\<forall>V \<in> rv S (CFG_node (targetnode a)). 
      fst cf\<^sub>1' V = state_val (transfer (slice_kind S a) s\<^sub>2) V" 
    proof
      fix V assume "V \<in> rv S (CFG_node (targetnode a))"
      show "fst cf\<^sub>1' V = state_val (transfer (slice_kind S a) s\<^sub>2) V"
      proof(cases "V \<in> Def (sourcenode a)")
        case True
        from `intra_kind (kind a)` have "(\<exists>f. kind a = \<Up>f) \<or> (\<exists>Q. kind a = (Q)\<^sub>\<surd>)" 
          by(simp add:intra_kind_def)
        thus ?thesis
        proof
          assume "\<exists>f. kind a = \<Up>f"
          then obtain f' where "kind a = \<Up>f'" by blast
          with `transfer (kind a) s\<^sub>1 = s\<^sub>1'`
          have "s\<^sub>1' = (f' (fst cf\<^sub>1),snd cf\<^sub>1) # cfs\<^sub>1" by simp
          from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = \<Up>f'`
          have "slice_kind S a = \<Up>f'"
            by(fastforce dest:slice_intra_kind_in_slice simp:intra_kind_def)
          hence "transfer (slice_kind S a) s\<^sub>2 = (f' (fst cf\<^sub>2),snd cf\<^sub>2) # cfs\<^sub>2" by simp
          from `valid_edge a` `\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V` 
            `intra_kind (kind a)` `pred (kind a) s\<^sub>1` `pred (kind a) s\<^sub>2`
          have "\<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s\<^sub>1) V =
            state_val (transfer (kind a) s\<^sub>2) V"
            by -(erule CFG_intra_edge_transfer_uses_only_Use,auto)
          with `kind a = \<Up>f'` `s\<^sub>1' = (f' (fst cf\<^sub>1),snd cf\<^sub>1) # cfs\<^sub>1` True
            `transfer (slice_kind S a) s\<^sub>2 = (f' (fst cf\<^sub>2),snd cf\<^sub>2) # cfs\<^sub>2`
          show ?thesis by simp
        next
          assume "\<exists>Q. kind a = (Q)\<^sub>\<surd>"
          then obtain Q where "kind a = (Q)\<^sub>\<surd>" by blast
          with `transfer (kind a) s\<^sub>1 = s\<^sub>1'` have "s\<^sub>1' = cf\<^sub>1 # cfs\<^sub>1" by simp
          from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>`
          have "slice_kind S a = (Q)\<^sub>\<surd>"
            by(fastforce dest:slice_intra_kind_in_slice simp:intra_kind_def)
          hence "transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2" by simp
          from `valid_edge a` `\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V` 
            `intra_kind (kind a)` `pred (kind a) s\<^sub>1` `pred (kind a) s\<^sub>2`
          have "\<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s\<^sub>1) V =
                                         state_val (transfer (kind a) s\<^sub>2) V"
            by -(erule CFG_intra_edge_transfer_uses_only_Use,auto simp:intra_kind_def)
          with True `kind a = (Q)\<^sub>\<surd>` `s\<^sub>1' = cf\<^sub>1 # cfs\<^sub>1`
            `transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2` 
          show ?thesis by simp
        qed
      next
        case False
        with `valid_edge a` `intra_kind (kind a)` `pred (kind a) s\<^sub>1`
        have "state_val (transfer (kind a) s\<^sub>1) V = state_val s\<^sub>1 V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        with `transfer (kind a) s\<^sub>1 = s\<^sub>1'` have "fst cf\<^sub>1' V = fst cf\<^sub>1 V" by simp
        from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `intra_kind (kind a)`
        have "slice_kind S a = kind a" by(fastforce intro:slice_intra_kind_in_slice)
        from False `valid_edge a` `pred (kind a) s\<^sub>2` `intra_kind (kind a)`
        have "state_val (transfer (kind a) s\<^sub>2) V = state_val s\<^sub>2 V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        with `slice_kind S a = kind a`
        have "state_val (transfer (slice_kind S a) s\<^sub>2) V = fst cf\<^sub>2 V" by simp
        from `V \<in> rv S (CFG_node (targetnode a))` obtain as' nx 
          where "targetnode a -as'\<rightarrow>\<^sub>\<iota>* parent_node nx" 
          and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
          and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as') 
                     \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        with `\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as') 
                    \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''` False
        have all:"\<forall>n''. valid_SDG_node n'' \<and> 
          parent_node n'' \<in> set (sourcenodes (a#as')) \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce dest:SDG_Def_parent_Def simp:sourcenodes_def)
        from  `valid_edge a` `targetnode a -as'\<rightarrow>\<^sub>\<iota>* parent_node nx` 
          `intra_kind (kind a)`
        have "sourcenode a -a#as'\<rightarrow>\<^sub>\<iota>* parent_node nx"
          by(fastforce intro:Cons_path simp:intra_path_def)
        with `nx \<in> HRB_slice S` `V \<in> Use\<^bsub>SDG\<^esub> nx` all
        have "V \<in> rv S (CFG_node (sourcenode a))" by(fastforce intro:rvI)
        with `\<forall>V \<in> rv S (CFG_node mx). (fst (s\<^sub>1!(length msx))) V = state_val s\<^sub>2 V`
          `state_val (transfer (slice_kind S a) s\<^sub>2) V = fst cf\<^sub>2 V`
          `fst cf\<^sub>1' V = fst cf\<^sub>1 V`
        show ?thesis by fastforce
      qed
    qed
    with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` cf2' 
      `ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2`
      `length ms\<^sub>1 = length s\<^sub>1` `length ms\<^sub>2 = length s\<^sub>2` `length s\<^sub>1 = length s\<^sub>2`
    have "\<forall>i<length ms\<^sub>1'. \<forall>V\<in>rv S (CFG_node ((targetnode a # tl ms\<^sub>1')!i)).
      (fst (s\<^sub>1'!(length [] + i))) V = (fst (transfer (slice_kind S a) s\<^sub>2 ! i)) V"
      by clarsimp(case_tac i,auto)
    with `\<forall>m \<in> set ms\<^sub>2. valid_node m` `\<forall>m \<in> set ms\<^sub>1'. valid_node m` 
      `length ms\<^sub>2 = length s\<^sub>2` `length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)`
      `length ms\<^sub>1' = length s\<^sub>1'` `\<forall>m \<in> set (tl ms\<^sub>1'). return_node m`
      `ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2` `get_proc mx = get_proc (hd ms\<^sub>2)`
      `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)`
    have "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
      by(fastforce intro!:WSI)
    with `S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)`
    show ?case by blast
  next
    case (observable_move_call a s\<^sub>1 s\<^sub>1' Q r p fs a' ms\<^sub>1 S ms\<^sub>1')
    from `s\<^sub>1 \<noteq> []` `s\<^sub>2 \<noteq> []` obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
      and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from `length ms\<^sub>1 = length s\<^sub>1` `s\<^sub>1 \<noteq> []` have [simp]:"ms\<^sub>1 \<noteq> []" by(cases ms\<^sub>1) auto
    from `length ms\<^sub>2 = length s\<^sub>2` `s\<^sub>2 \<noteq> []` have [simp]:"ms\<^sub>2 \<noteq> []" by(cases ms\<^sub>2) auto
    from `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `hd ms\<^sub>1 = sourcenode a` `ms\<^sub>1 = msx@mx#tl ms\<^sub>2`
      `msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
    have [simp]:"mx = sourcenode a" "msx = []" and [simp]:"tl ms\<^sub>2 = tl ms\<^sub>1"
      by(cases msx,auto)+
    hence "length ms\<^sub>1 = length ms\<^sub>2" by(cases ms\<^sub>2) auto
    with `length ms\<^sub>1 = length s\<^sub>1` `length ms\<^sub>2 = length s\<^sub>2`
    have "length s\<^sub>1 = length s\<^sub>2" by simp
    from `hd ms\<^sub>1 \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `hd ms\<^sub>1 = sourcenode a`
    have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with `valid_edge a` 
    have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
      by(fastforce intro!:n_in_obs_intra)
    from `\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}` 
      `hd ms\<^sub>1 = sourcenode a` 
    have "(hd ms\<^sub>1#tl ms\<^sub>1) \<in> obs ([]@hd ms\<^sub>1#tl ms\<^sub>1) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(cases ms\<^sub>1)(auto intro!:obsI)
    hence "ms\<^sub>1 \<in> obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with `obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    from `ms\<^sub>2 \<noteq> []` `length ms\<^sub>2 = length s\<^sub>2` have "length s\<^sub>2 = length (hd ms\<^sub>2#tl ms\<^sub>2)"
      by(fastforce dest!:hd_Cons_tl)
    from `\<forall>m \<in> set (tl ms\<^sub>1). return_node m` have "\<forall>m \<in> set (tl ms\<^sub>2). return_node m"
      by simp
    with `ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "hd ms\<^sub>1 \<in> obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof(rule obsE)
      fix nsx n nsx' n'
      assume "ms\<^sub>2 = nsx @ n # nsx'" and "ms\<^sub>1 = n' # nsx'"
        and "n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      from `ms\<^sub>2 = nsx @ n # nsx'` `ms\<^sub>1 = n' # nsx'` `tl ms\<^sub>2 = tl ms\<^sub>1`
      have [simp]:"nsx = []" by(cases nsx) auto
      with `ms\<^sub>2 = nsx @ n # nsx'` have [simp]:"n = hd ms\<^sub>2" by simp
      from `ms\<^sub>1 = n' # nsx'` have [simp]:"n' = hd ms\<^sub>1" by simp
      with `n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` show ?thesis by simp
    qed
    with `length s\<^sub>2 = length (hd ms\<^sub>2#tl ms\<^sub>2)` `\<forall>m \<in> set (tl ms\<^sub>2). return_node m`
    obtain as where "S,slice_kind S \<turnstile> (hd ms\<^sub>2#tl ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (hd ms\<^sub>1#tl ms\<^sub>1,s\<^sub>2)"
      by(fastforce elim:silent_moves_intra_path_obs[of _ _ _ s\<^sub>2 "tl ms\<^sub>2"])
    with `ms\<^sub>2 \<noteq> []` have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
      by(fastforce dest!:hd_Cons_tl)
    from `valid_edge a` have "valid_node (sourcenode a)" by simp
    hence "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
      by(fastforce intro:empty_path simp:intra_path_def)
    with `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "\<forall>V. V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a)) 
      \<longrightarrow> V \<in> rv S (CFG_node (sourcenode a))"
      by auto(rule rvI,auto simp:SDG_to_CFG_set_def sourcenodes_def)
    with `valid_node (sourcenode a)`
    have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
      by(fastforce intro:CFG_Use_SDG_Use)
    from `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` `length ms\<^sub>2 = length s\<^sub>2`
    have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
      by(cases ms\<^sub>2) auto
    with `\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))`
    have "\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V" by fastforce
    moreover
    from `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)`
    have "snd (hd s\<^sub>1) = snd (hd s\<^sub>2)" by(erule_tac x="0" in allE) auto
    ultimately have "pred (kind a) s\<^sub>2"
      using `valid_edge a` `pred (kind a) s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2`
      by(fastforce intro:CFG_edge_Uses_pred_equal)
    from `ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1` `length s\<^sub>1' = Suc(length s\<^sub>1)` 
      `length ms\<^sub>1 = length s\<^sub>1` have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain ins outs 
      where "(p,ins,outs) \<in> set procs" by(fastforce dest!:callee_in_procs)
    with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
    have "(THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins"
      by(rule formal_in_THE)
    with `transfer (kind a) s\<^sub>1 = s\<^sub>1'` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have [simp]:"s\<^sub>1' = (empty(ins [:=] params fs (fst cf\<^sub>1)),r)#cf\<^sub>1#cfs\<^sub>1" by simp
    from `valid_edge a'` `a' \<in> get_return_edges a` `valid_edge a`
    have "return_node (targetnode a')" by(fastforce simp:return_node_def)
    with `valid_edge a` `valid_edge a'` `a' \<in> get_return_edges a`
    have "call_of_return_node (targetnode a') (sourcenode a)"
      by(simp add:call_of_return_node_def) blast
    from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `pred (kind a) s\<^sub>2` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "pred (slice_kind S a) s\<^sub>2" by(fastforce dest:slice_kind_Call_in_slice)
    from `valid_edge a` `length s\<^sub>1 = length s\<^sub>2` `transfer (kind a) s\<^sub>1 = s\<^sub>1'`
    have "length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)"
      by(fastforce intro:length_transfer_kind_slice_kind)
    with `pred (slice_kind S a) s\<^sub>2` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `hd ms\<^sub>1 \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `hd ms\<^sub>1 = sourcenode a`
      `length ms\<^sub>1 = length s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2` `valid_edge a'`
      `ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1` `a' \<in> get_return_edges a`
      `\<forall>m \<in> set (tl ms\<^sub>2). return_node m`
    have "S,slice_kind S \<turnstile> (ms\<^sub>1,s\<^sub>2) -a\<rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(auto intro:observable_move.observable_move_call)
    with `S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)` 
    have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(rule observable_moves_snoc)
    from `\<forall>m \<in> set ms\<^sub>1. valid_node m` `ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1`
      `valid_edge a` `valid_edge a'`
    have "\<forall>m \<in> set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have cf2':"\<exists>cf\<^sub>2'. transfer (slice_kind S a) s\<^sub>2 = cf\<^sub>2'#s\<^sub>2 \<and> snd cf\<^sub>2' = r"
      by(auto dest:slice_kind_Call_in_slice)
    with `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)` 
      `length ms\<^sub>1' = length s\<^sub>1'` `msx = []` `length ms\<^sub>1 = length ms\<^sub>2`
      `length ms\<^sub>1 = length s\<^sub>1`
    have "\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)"
      by auto(case_tac i,auto)
    have "\<forall>V \<in> rv S (CFG_node (targetnode a')). 
      V \<in> rv S (CFG_node (sourcenode a))"
    proof
      fix V assume "V \<in> rv S (CFG_node (targetnode a'))"
      then obtain as n' where "targetnode a' -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
        and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
        and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
      from `valid_edge a` `a' \<in> get_return_edges a`
      obtain a'' where "valid_edge a''" and "sourcenode a'' = sourcenode a"
        and "targetnode a'' = targetnode a'" and "intra_kind(kind a'')"
        by -(drule call_return_node_edge,auto simp:intra_kind_def)
      with `targetnode a' -as\<rightarrow>\<^sub>\<iota>* parent_node n'` 
      have "sourcenode a -a''#as\<rightarrow>\<^sub>\<iota>* parent_node n'"
        by(fastforce intro:Cons_path simp:intra_path_def)
      from `sourcenode a'' = sourcenode a` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' = sourcenode a''
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
        by(fastforce dest:SDG_Def_parent_Def call_source_Def_empty)
      with `\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''`
      have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (a''#as)) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce simp:sourcenodes_def)
      with `sourcenode a -a''#as\<rightarrow>\<^sub>\<iota>* parent_node n'` `n' \<in> HRB_slice S`
        `V \<in> Use\<^bsub>SDG\<^esub> n'`
      show "V \<in> rv S (CFG_node (sourcenode a))" by(fastforce intro:rvI)
    qed
    have "\<forall>V \<in> rv S (CFG_node (targetnode a)). 
      (empty(ins [:=] params fs (fst cf\<^sub>1))) V = 
      state_val (transfer (slice_kind S a) s\<^sub>2) V"
    proof
      fix V assume "V \<in> rv S (CFG_node (targetnode a))"
      from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        `(THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins`
      have eq:"fst (hd (transfer (slice_kind S a) s\<^sub>2)) = 
        empty(ins [:=] params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))"
        by(auto dest:slice_kind_Call_in_slice)
      show "(empty(ins [:=] params fs (fst cf\<^sub>1))) V = 
        state_val (transfer (slice_kind S a) s\<^sub>2) V"
      proof(cases "V \<in> set ins")
        case True
        then obtain i where "V = ins!i" and "i < length ins"
          by(auto simp:in_set_conv_nth)
        from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
          `i < length ins`
        have "valid_SDG_node (Formal_in (targetnode a,i))" by fastforce
        from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc(targetnode a) = p"
          by(rule get_proc_call)
        with `valid_SDG_node (Formal_in (targetnode a,i))` 
          `(p,ins,outs) \<in> set procs` `V = ins!i`
        have "V \<in> Def\<^bsub>SDG\<^esub> (Formal_in (targetnode a,i))"
          by(fastforce intro:Formal_in_SDG_Def)
        from `V \<in> rv S (CFG_node (targetnode a))` obtain as' nx 
          where "targetnode a -as'\<rightarrow>\<^sub>\<iota>* parent_node nx" 
          and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
          and "\<forall>n''. valid_SDG_node n'' \<and> 
          parent_node n'' \<in> set (sourcenodes as') \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        with `valid_SDG_node (Formal_in (targetnode a,i))`
          `V \<in> Def\<^bsub>SDG\<^esub> (Formal_in (targetnode a,i))`
        have "targetnode a = parent_node nx" 
          apply(auto simp:intra_path_def sourcenodes_def)
          apply(erule path.cases) apply fastforce
          apply(erule_tac x="Formal_in (targetnode a,i)" in allE) by fastforce
        with `V \<in> Use\<^bsub>SDG\<^esub> nx` have "V \<in> Use (targetnode a)"
          by(fastforce intro:SDG_Use_parent_Use)
        with `valid_edge a` have "V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (targetnode a))"
          by(auto intro!:CFG_Use_SDG_Use)
        from `targetnode a = parent_node nx`[THEN sym] `valid_edge a`
        have "parent_node (Formal_in (targetnode a,i)) -[]\<rightarrow>\<^sub>\<iota>* parent_node nx"
          by(fastforce intro:empty_path simp:intra_path_def)
        with `V \<in> Def\<^bsub>SDG\<^esub> (Formal_in (targetnode a,i))` 
          `V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (targetnode a))` `targetnode a = parent_node nx`
        have "Formal_in (targetnode a,i) influences V in (CFG_node (targetnode a))"
          by(fastforce simp:data_dependence_def sourcenodes_def)
        hence ddep:"Formal_in (targetnode a,i) s-V\<rightarrow>\<^bsub>dd\<^esub> (CFG_node (targetnode a))"
          by(rule sum_SDG_ddep_edge)
        from `targetnode a = parent_node nx` `nx \<in> HRB_slice S`
        have "CFG_node (targetnode a) \<in> HRB_slice S"
          by(fastforce dest:valid_SDG_node_in_slice_parent_node_in_slice)
        hence "Formal_in (targetnode a,i) \<in> HRB_slice S"
        proof(induct "CFG_node (targetnode a)" rule:HRB_slice_cases)
          case (phase1 nx)
          with ddep show ?case
            by(fastforce intro:ddep_slice1 combine_SDG_slices.combSlice_refl 
                         simp:HRB_slice_def)
        next
          case (phase2 nx n' n'' p)
          from `CFG_node (targetnode a) \<in> sum_SDG_slice2 n'` ddep
          have "Formal_in (targetnode a,i) \<in> sum_SDG_slice2 n'"
            by(fastforce intro:ddep_slice2)
          with `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')` `n' \<in> sum_SDG_slice1 nx` 
            `nx \<in> S`
          show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node                                  simp:HRB_slice_def)
        qed
        from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        have slice_kind:"slice_kind S a = 
          Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)"
          by(rule slice_kind_Call_in_slice)
        from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
        have "length fs = length ins" by(rule CFG_call_edge_length)
        from `Formal_in (targetnode a,i) \<in> HRB_slice S`
          `length fs = length ins` `i < length ins`
        have cspp:"(cspp (targetnode a) (HRB_slice S) fs)!i = fs!i"
          by(fastforce intro:csppa_Formal_in_in_slice simp:cspp_def)
        from `i < length ins` `length fs = length ins`
        have "(params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))!i = 
          ((cspp (targetnode a) (HRB_slice S) fs)!i) (fst cf\<^sub>2)"
          by(fastforce intro:params_nth)
        with cspp 
        have eq:"(params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))!i =
          (fs!i) (fst cf\<^sub>2)" by simp
        from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
        have "(THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins"
          by(rule formal_in_THE)
        with slice_kind
        have "fst (hd (transfer (slice_kind S a) s\<^sub>2)) = 
          empty(ins [:=] params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))"
          by simp
        moreover
        from `(p,ins,outs) \<in> set procs` have "distinct ins" 
          by(rule distinct_formal_ins)
        ultimately have "state_val (transfer (slice_kind S a) s\<^sub>2) V = 
          (params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))!i"
          using `V = ins!i` `i < length ins` `length fs = length ins`
          by(fastforce intro:fun_upds_nth)
        with eq 
        have 2:"state_val (transfer (slice_kind S a) s\<^sub>2) V = (fs!i) (fst cf\<^sub>2)"
          by simp
        from `V = ins!i` `i < length ins` `length fs = length ins`
          `distinct ins`
        have "empty(ins [:=] params fs (fst cf\<^sub>1)) V = (params fs (fst cf\<^sub>1))!i"
          by(fastforce intro:fun_upds_nth)
        with `i < length ins` `length fs = length ins`
        have 1:"empty(ins [:=] params fs (fst cf\<^sub>1)) V = (fs!i) (fst cf\<^sub>1)"
          by(fastforce intro:params_nth)
        from `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
          (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V`
        have rv:"\<forall>V\<in>rv S (CFG_node (sourcenode a)). fst cf\<^sub>1 V = fst cf\<^sub>2 V"
          by(erule_tac x="0" in allE) auto
        from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs` 
          `i < length ins` have "\<forall>V\<in>(ParamUses (sourcenode a)!i). 
          V \<in> Use\<^bsub>SDG\<^esub> (Actual_in (sourcenode a,i))"
          by(fastforce intro:Actual_in_SDG_Use)
        with `valid_edge a` have "\<forall>V\<in>(ParamUses (sourcenode a)!i). 
          V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a))"
          by(auto intro!:CFG_Use_SDG_Use dest:SDG_Use_parent_Use)
        moreover
        from `valid_edge a` have "parent_node (CFG_node (sourcenode a)) -[]\<rightarrow>\<^sub>\<iota>* 
          parent_node (CFG_node (sourcenode a))"
          by(fastforce intro:empty_path simp:intra_path_def)
        ultimately 
        have "\<forall>V\<in>(ParamUses (sourcenode a)!i). V \<in> rv S (CFG_node (sourcenode a))"
          using `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `valid_edge a`
          by(fastforce intro:rvI simp:SDG_to_CFG_set_def sourcenodes_def)
        with rv have "\<forall>V \<in> (ParamUses (sourcenode a))!i. fst cf\<^sub>1 V = fst cf\<^sub>2 V"
          by fastforce
        with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `i < length ins`
          `(p,ins,outs) \<in> set procs` `pred (kind a) s\<^sub>1` `pred (kind a) s\<^sub>2`
        have "(params fs (fst cf\<^sub>1))!i = (params fs (fst cf\<^sub>2))!i"
          by(fastforce dest!:CFG_call_edge_params)
        moreover
        from `i < length ins` `length fs = length ins`
        have "(params fs (fst cf\<^sub>1))!i = (fs!i) (fst cf\<^sub>1)" 
          and "(params fs (fst cf\<^sub>2))!i = (fs!i) (fst cf\<^sub>2)"
          by(auto intro:params_nth)
        ultimately show ?thesis using 1 2 by simp
      next
        case False
        with eq show ?thesis by(fastforce simp:fun_upds_notin)
      qed
    qed
    with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` cf2' `tl ms\<^sub>2 = tl ms\<^sub>1`
      `length ms\<^sub>2 = length s\<^sub>2` `length ms\<^sub>1 = length s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2`
      `ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1`
      `\<forall>V \<in> rv S (CFG_node (targetnode a')). V \<in> rv S (CFG_node (sourcenode a))`
    have "\<forall>i<length ms\<^sub>1'. \<forall>V\<in>rv S (CFG_node ((targetnode a # tl ms\<^sub>1')!i)).
      (fst (s\<^sub>1'!(length [] + i))) V = (fst (transfer (slice_kind S a) s\<^sub>2!i)) V"
      apply clarsimp apply(case_tac i) apply auto
      apply(erule_tac x="nat" in allE)
      apply(case_tac nat) apply auto done
    with `\<forall>m \<in> set ms\<^sub>2. valid_node m` `\<forall>m \<in> set ms\<^sub>1'. valid_node m` 
      `length ms\<^sub>2 = length s\<^sub>2` `length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)`
      `length ms\<^sub>1' = length s\<^sub>1'` `ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1`
      `get_proc mx = get_proc (hd ms\<^sub>2)` `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `return_node (targetnode a')` `\<forall>m \<in> set (tl ms\<^sub>1). return_node m`
      `call_of_return_node (targetnode a') (sourcenode a)`
      `\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)`
    have "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
      by(fastforce intro!:WSI)
    with `S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)`
    show ?case by blast
  next
    case (observable_move_return a s\<^sub>1 s\<^sub>1' Q p f' ms\<^sub>1 S ms\<^sub>1')
    from `s\<^sub>1 \<noteq> []` `s\<^sub>2 \<noteq> []` obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
      and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from `length ms\<^sub>1 = length s\<^sub>1` `s\<^sub>1 \<noteq> []` have [simp]:"ms\<^sub>1 \<noteq> []" by(cases ms\<^sub>1) auto
    from `length ms\<^sub>2 = length s\<^sub>2` `s\<^sub>2 \<noteq> []` have [simp]:"ms\<^sub>2 \<noteq> []" by(cases ms\<^sub>2) auto
    from `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `hd ms\<^sub>1 = sourcenode a` `ms\<^sub>1 = msx@mx#tl ms\<^sub>2`
      `msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)`
    have [simp]:"mx = sourcenode a" "msx = []" and [simp]:"tl ms\<^sub>2 = tl ms\<^sub>1"
      by(cases msx,auto)+
    hence "length ms\<^sub>1 = length ms\<^sub>2" by(cases ms\<^sub>2) auto
    with `length ms\<^sub>1 = length s\<^sub>1` `length ms\<^sub>2 = length s\<^sub>2`
    have "length s\<^sub>1 = length s\<^sub>2" by simp
    have "\<exists>as. S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
    proof(cases "obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}")
      case True
      from `valid_edge a` `hd ms\<^sub>1 = sourcenode a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
      have "method_exit (hd ms\<^sub>1)" by(fastforce simp:method_exit_def)
      from `\<forall>m\<in>set ms\<^sub>2. valid_node m` have "valid_node (hd ms\<^sub>2)" by(cases ms\<^sub>2) auto
      then obtain asx where "hd ms\<^sub>2 -asx\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(fastforce dest!:Exit_path)
      then obtain as pex where "hd ms\<^sub>2 -as\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
        by(fastforce elim:valid_Exit_path_intra_path)
      from `hd ms\<^sub>2 -as\<rightarrow>\<^sub>\<iota>* pex` have "get_proc (hd ms\<^sub>2) = get_proc pex"
        by(rule intra_path_get_procs)
      with `get_proc mx = get_proc (hd ms\<^sub>2)`
      have "get_proc mx = get_proc pex" by simp
      with `method_exit (hd ms\<^sub>1)` ` hd ms\<^sub>1 = sourcenode a` `method_exit pex`
      have [simp]:"pex = hd ms\<^sub>1" by(fastforce intro:method_exit_unique)
      from `obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` `method_exit pex`
        `get_proc (hd ms\<^sub>2) = get_proc pex` `valid_node (hd ms\<^sub>2)`
        `length ms\<^sub>2 = length s\<^sub>2` `\<forall>m\<in>set (tl ms\<^sub>1). return_node m` `ms\<^sub>2 \<noteq> []`
      obtain as' 
        where "S,slice_kind S \<turnstile> (hd ms\<^sub>2#tl ms\<^sub>2,s\<^sub>2) =as'\<Rightarrow>\<^sub>\<tau> (hd ms\<^sub>1#tl ms\<^sub>1,s\<^sub>2)"
        by(fastforce elim!:silent_moves_intra_path_no_obs[of _ _ _ s\<^sub>2 "tl ms\<^sub>2"]
                     dest:hd_Cons_tl)
      with `ms\<^sub>2 \<noteq> []` have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as'\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
        by(fastforce dest!:hd_Cons_tl)
      thus ?thesis by blast
    next
      case False
      then obtain x where "x \<in> obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      hence "obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {x}"
        by(rule obs_intra_singleton_element)
      with `\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "x#tl ms\<^sub>1 \<in> obs ([]@hd ms\<^sub>2#tl ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(fastforce intro:obsI)
      with `ms\<^sub>2 \<noteq> []` have "x#tl ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(fastforce dest:hd_Cons_tl simp del:obs.simps)
      with `obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "x#tl ms\<^sub>1 \<in> obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from this `\<forall>m\<in>set (tl ms\<^sub>1). return_node m`
      have "x \<in> obs_intra (hd ms\<^sub>1) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      proof(rule obsE)
        fix nsx n nsx' n'
        assume "ms\<^sub>1 = nsx @ n # nsx'" and "x # tl ms\<^sub>1 = n' # nsx'"
          and "n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        from `ms\<^sub>1 = nsx @ n # nsx'` `x # tl ms\<^sub>1 = n' # nsx'` `tl ms\<^sub>2 = tl ms\<^sub>1`
        have [simp]:"nsx = []" by(cases nsx) auto
        with `ms\<^sub>1 = nsx @ n # nsx'` have [simp]:"n = hd ms\<^sub>1" by simp
        from `x # tl ms\<^sub>1 = n' # nsx'` have [simp]:"n' = x" by simp
        with `n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` show ?thesis by simp
      qed
      { fix m as assume "hd ms\<^sub>1 -as\<rightarrow>\<^sub>\<iota>* m"
        hence "hd ms\<^sub>1 -as\<rightarrow>* m" and "\<forall>a \<in> set as. intra_kind (kind a)"
          by(simp_all add:intra_path_def)
        hence "m = hd ms\<^sub>1"
        proof(induct "hd ms\<^sub>1" as m rule:path.induct)
          case (Cons_path m'' as' m' a')
          from `\<forall>a\<in>set (a' # as'). intra_kind (kind a)`
          have "intra_kind (kind a')" by simp
          with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `valid_edge a'` 
            `sourcenode a' = hd ms\<^sub>1` `hd ms\<^sub>1 = sourcenode a`
          have False by(fastforce dest:return_edges_only simp:intra_kind_def)
          thus ?case by simp
        qed simp }
      with `x \<in> obs_intra (hd ms\<^sub>1) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "x = hd ms\<^sub>1" by(fastforce elim:obs_intraE)
      with `x \<in> obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `length ms\<^sub>2 = length s\<^sub>2` 
        `\<forall>m\<in>set (tl ms\<^sub>1). return_node m` `ms\<^sub>2 \<noteq> []`
      obtain as where "S,slice_kind S \<turnstile> (hd ms\<^sub>2#tl ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (hd ms\<^sub>1#tl ms\<^sub>1,s\<^sub>2)"
        by(fastforce elim!:silent_moves_intra_path_obs[of _ _ _ s\<^sub>2 "tl ms\<^sub>2"] 
                     dest:hd_Cons_tl)
      with `ms\<^sub>2 \<noteq> []` have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
        by(fastforce dest!:hd_Cons_tl)
      thus ?thesis by blast
    qed
    then obtain as where "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)" by blast
    from `ms\<^sub>1' = tl ms\<^sub>1` `length s\<^sub>1 = Suc(length s\<^sub>1')` 
      `length ms\<^sub>1 = length s\<^sub>1` have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` obtain a'' Q' r' fs' where "valid_edge a''"
      and "kind a'' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'" and "a \<in> get_return_edges a''"
      by -(drule return_needs_call,auto)
    then obtain ins outs where "(p,ins,outs) \<in> set procs"
      by(fastforce dest!:callee_in_procs)
    from `length s\<^sub>1 = Suc(length s\<^sub>1')` `s\<^sub>1' \<noteq> []`
    obtain cfx cfsx where [simp]:"cfs\<^sub>1 = cfx#cfsx" by(cases cfs\<^sub>1) auto
    with `length s\<^sub>1 = length s\<^sub>2` obtain cfx' cfsx' where [simp]:"cfs\<^sub>2 = cfx'#cfsx'"
      by(cases cfs\<^sub>2) auto
    from `length ms\<^sub>1 = length s\<^sub>1` have "tl ms\<^sub>1 = []@hd(tl ms\<^sub>1)#tl(tl ms\<^sub>1)"
      by(auto simp:length_Suc_conv)
    from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `transfer (kind a) s\<^sub>1 = s\<^sub>1'`
    have "s\<^sub>1' = (f' (fst cf\<^sub>1) (fst cfx),snd cfx)#cfsx" by simp
    from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p,ins,outs) \<in> set procs`
    have "f' (fst cf\<^sub>1) (fst cfx) = 
      (fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs)"
      by(rule CFG_return_edge_fun)
    with `s\<^sub>1' = (f' (fst cf\<^sub>1) (fst cfx),snd cfx)#cfsx`
    have [simp]:"s\<^sub>1' = 
      ((fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs),snd cfx)#cfsx"
      by simp
    have "pred (slice_kind S a) s\<^sub>2"
    proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      from `valid_edge a` have "valid_node (sourcenode a)" by simp
      hence "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
        by(fastforce intro:empty_path simp:intra_path_def)
      with `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "\<forall>V. V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a)) 
        \<longrightarrow> V \<in> rv S (CFG_node (sourcenode a))"
        by auto(rule rvI,auto simp:SDG_to_CFG_set_def sourcenodes_def)
      with `valid_node (sourcenode a)`
      have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
        by(fastforce intro:CFG_Use_SDG_Use)
      from `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` `length ms\<^sub>2 = length s\<^sub>2`
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
        by(cases ms\<^sub>2) auto
      with `\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))`
      have "\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V" by fastforce
      moreover
      from `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)`
      have "snd (hd s\<^sub>1) = snd (hd s\<^sub>2)" by(erule_tac x="0" in allE) auto
      ultimately have "pred (kind a) s\<^sub>2"
        using `valid_edge a` `pred (kind a) s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2`
        by(fastforce intro:CFG_edge_Uses_pred_equal)
      with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p,ins,outs) \<in> set procs` 
        `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      show ?thesis by(fastforce dest:slice_kind_Return_in_slice)
    next
      case False
      with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` have "slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')"
        by -(rule slice_kind_Return)
      thus ?thesis by simp
    qed
    from `valid_edge a` `length s\<^sub>1 = length s\<^sub>2` `transfer (kind a) s\<^sub>1 = s\<^sub>1'`
    have "length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)"
      by(fastforce intro:length_transfer_kind_slice_kind)
    with `pred (slice_kind S a) s\<^sub>2` `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
      `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `hd ms\<^sub>1 = sourcenode a`
      `length ms\<^sub>1 = length s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2`
      `ms\<^sub>1' = tl ms\<^sub>1` `hd(tl ms\<^sub>1) = targetnode a` `\<forall>m \<in> set (tl ms\<^sub>1). return_node m`
    have "S,slice_kind S \<turnstile> (ms\<^sub>1,s\<^sub>2) -a\<rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(fastforce intro!:observable_move.observable_move_return)
    with `S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)`
    have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(rule observable_moves_snoc)
    from `\<forall>m \<in> set ms\<^sub>1. valid_node m` `ms\<^sub>1' = tl ms\<^sub>1`
    have "\<forall>m \<in> set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from `length ms\<^sub>1' = length s\<^sub>1'` have "ms\<^sub>1' = []@hd ms\<^sub>1'#tl ms\<^sub>1'"
      by(cases ms\<^sub>1') auto
    from `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)`
      `length ms\<^sub>1 = length ms\<^sub>2` `length ms\<^sub>1 = length s\<^sub>1`
    have "snd cfx = snd cfx'" by(erule_tac x="1" in allE) auto
    from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p,ins,outs) \<in> set procs`
    have cf2':"\<exists>cf\<^sub>2'. transfer (slice_kind S a) s\<^sub>2 = cf\<^sub>2'#cfsx' \<and> snd cf\<^sub>2' = snd cfx'"
      by(cases cfx',cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>",
         auto dest:slice_kind_Return slice_kind_Return_in_slice)
    with `\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)` 
      `length ms\<^sub>1' = length s\<^sub>1'` `msx = []` `length ms\<^sub>1 = length ms\<^sub>2`
      `length ms\<^sub>1 = length s\<^sub>1` `snd cfx = snd cfx'`
    have "\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)"
      apply auto apply(case_tac i) apply auto
      by(erule_tac x="Suc(Suc nat)" in allE) auto
    from `\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "\<forall>m \<in> set (tl (tl ms\<^sub>1)). 
      \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(cases "tl ms\<^sub>1") auto
    from `\<forall>m \<in> set (tl ms\<^sub>1). return_node m`
    have "\<forall>m \<in> set (tl (tl ms\<^sub>1)). return_node m" by(cases "tl ms\<^sub>1") auto
    have "\<forall>V\<in>rv S (CFG_node (hd (tl ms\<^sub>1))).
      (fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = 
      state_val (transfer (slice_kind S a) s\<^sub>2) V"
    proof
      fix V assume "V\<in>rv S (CFG_node (hd (tl ms\<^sub>1)))"
      with `hd(tl ms\<^sub>1) = targetnode a` have "V\<in>rv S (CFG_node (targetnode a))"
        by simp
      show "(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = 
        state_val (transfer (slice_kind S a) s\<^sub>2) V"
      proof(cases "V \<in> set (ParamDefs (targetnode a))")
        case True
        then obtain i where "V = (ParamDefs (targetnode a))!i" 
          and "i < length(ParamDefs (targetnode a))"
          by(auto simp:in_set_conv_nth)
        moreover
        from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p,ins,outs) \<in> set procs`
        have length:"length(ParamDefs (targetnode a)) = length outs"
          by(fastforce intro:ParamDefs_return_target_length)
        from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p,ins,outs) \<in> set procs`
          `i < length(ParamDefs (targetnode a))` 
          `length(ParamDefs (targetnode a)) = length outs`
        have "valid_SDG_node (Actual_out(targetnode a,i))" by fastforce
        with `V = (ParamDefs (targetnode a))!i`
        have "V \<in> Def\<^bsub>SDG\<^esub> (Actual_out(targetnode a,i))"
          by(fastforce intro:Actual_out_SDG_Def)
        from `V \<in> rv S (CFG_node (targetnode a))` obtain as' nx 
          where "targetnode a -as'\<rightarrow>\<^sub>\<iota>* parent_node nx" 
          and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
          and "\<forall>n''. valid_SDG_node n'' \<and> 
                         parent_node n'' \<in> set (sourcenodes as') \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        with `valid_SDG_node (Actual_out(targetnode a,i))`
          `V \<in> Def\<^bsub>SDG\<^esub> (Actual_out(targetnode a,i))`
        have "targetnode a = parent_node nx" 
          apply(auto simp:intra_path_def sourcenodes_def)
          apply(erule path.cases) apply fastforce
          apply(erule_tac x="(Actual_out(targetnode a,i))" in allE) by fastforce
        with `V \<in> Use\<^bsub>SDG\<^esub> nx` have "V \<in> Use (targetnode a)"
          by(fastforce intro:SDG_Use_parent_Use)
        with `valid_edge a` have "V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (targetnode a))"
          by(auto intro!:CFG_Use_SDG_Use)
        from `targetnode a = parent_node nx`[THEN sym] `valid_edge a`
        have "parent_node (Actual_out(targetnode a,i)) -[]\<rightarrow>\<^sub>\<iota>* parent_node nx"
          by(fastforce intro:empty_path simp:intra_path_def)
        with `V \<in> Def\<^bsub>SDG\<^esub> (Actual_out(targetnode a,i))` 
          `V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (targetnode a))` `targetnode a = parent_node nx`
        have "Actual_out(targetnode a,i) influences V in (CFG_node (targetnode a))"
          by(fastforce simp:data_dependence_def sourcenodes_def)
        hence ddep:"Actual_out(targetnode a,i) s-V\<rightarrow>\<^bsub>dd\<^esub> (CFG_node (targetnode a))"
          by(rule sum_SDG_ddep_edge)
        from `targetnode a = parent_node nx` `nx \<in> HRB_slice S`
        have "CFG_node (targetnode a) \<in> HRB_slice S"
          by(fastforce dest:valid_SDG_node_in_slice_parent_node_in_slice)
        hence "Actual_out(targetnode a,i) \<in> HRB_slice S"
        proof(induct "CFG_node (targetnode a)" rule:HRB_slice_cases)
          case (phase1 nx')
          with ddep show ?case
            by(fastforce intro: ddep_slice1 combine_SDG_slices.combSlice_refl
                         simp:HRB_slice_def)
        next
          case (phase2 nx' n' n'' p)
          from `CFG_node (targetnode a) \<in> sum_SDG_slice2 n'` ddep
          have "Actual_out(targetnode a,i) \<in> sum_SDG_slice2 n'"
            by(fastforce intro:ddep_slice2)
          with `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')` `n' \<in> sum_SDG_slice1 nx'`
            `nx' \<in> S`
          show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node
                                  simp:HRB_slice_def)
        qed
        from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `valid_edge a''`
          `kind a'' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'` `a \<in> get_return_edges a''`
          `CFG_node (targetnode a) \<in> HRB_slice S`
        have "CFG_node (sourcenode a) \<in> HRB_slice S"
          by(rule call_return_nodes_in_slice)
        hence "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(simp add:SDG_to_CFG_set_def)
        from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
          `(p,ins,outs) \<in> set procs`
        have slice_kind:"slice_kind S a = 
          Q\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. rspp (targetnode a) (HRB_slice S) outs cf' cf)"
          by(rule slice_kind_Return_in_slice)
        from `Actual_out(targetnode a,i) \<in> HRB_slice S`
          `i < length(ParamDefs (targetnode a))` `valid_edge a`
          `V = (ParamDefs (targetnode a))!i` length
        have 2:"rspp (targetnode a) (HRB_slice S) outs (fst cfx') (fst cf\<^sub>2) V = 
          (fst cf\<^sub>2)(outs!i)"
          by(fastforce intro:rspp_Actual_out_in_slice)
        from `i < length(ParamDefs (targetnode a))` length `valid_edge a`
        have "(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) 
          ((ParamDefs (targetnode a))!i) = (map (fst cf\<^sub>1) outs)!i"
          by(fastforce intro:fun_upds_nth distinct_ParamDefs)
        with `V = (ParamDefs (targetnode a))!i` 
          `i < length(ParamDefs (targetnode a))` length
        have 1:"(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = 
          (fst cf\<^sub>1)(outs!i)" 
          by simp
        from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p,ins,outs) \<in> set procs` 
          `i < length(ParamDefs (targetnode a))` length
        have po:"Formal_out(sourcenode a,i) s-p:outs!i\<rightarrow>\<^bsub>out\<^esub> Actual_out(targetnode a,i)"
          by(fastforce intro:sum_SDG_param_out_edge)
        from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
        have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)"
          by(fastforce intro:sum_SDG_return_edge)
        from `Actual_out(targetnode a,i) \<in> HRB_slice S`
        have "Formal_out(sourcenode a,i) \<in> HRB_slice S"
        proof(induct "Actual_out(targetnode a,i)" rule:HRB_slice_cases)
          case (phase1 nx')
          let ?AO = "Actual_out(targetnode a,i)"
          from `valid_SDG_node ?AO` have "?AO \<in> sum_SDG_slice2 ?AO"
            by(rule refl_slice2)
          with po have "Formal_out(sourcenode a,i) \<in> sum_SDG_slice2 ?AO"
            by(rule param_out_slice2)
          with `CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)`
            `Actual_out (targetnode a, i) \<in> sum_SDG_slice1 nx'` `nx' \<in> S`
          show ?case
            by(fastforce intro:combSlice_Return_parent_node simp:HRB_slice_def)
        next
          case (phase2 nx' n' n'' p)
          from `Actual_out (targetnode a, i) \<in> sum_SDG_slice2 n'` po
          have "Formal_out(sourcenode a,i) \<in> sum_SDG_slice2 n'"
            by(fastforce intro:param_out_slice2)
          with `n' \<in> sum_SDG_slice1 nx'` `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')` 
            `nx' \<in> S`
          show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node
                                  simp:HRB_slice_def)
        qed
        with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p,ins,outs) \<in> set procs` 
          `i < length(ParamDefs (targetnode a))` length
        have "outs!i \<in> Use\<^bsub>SDG\<^esub> Formal_out(sourcenode a,i)"
          by(fastforce intro!:Formal_out_SDG_Use get_proc_return)
        with `valid_edge a` have "outs!i \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a))"
          by(auto intro!:CFG_Use_SDG_Use dest:SDG_Use_parent_Use)
        moreover
        from `valid_edge a` have "parent_node (CFG_node (sourcenode a)) -[]\<rightarrow>\<^sub>\<iota>* 
          parent_node (CFG_node (sourcenode a))"
          by(fastforce intro:empty_path simp:intra_path_def)
        ultimately have "outs!i \<in> rv S (CFG_node (sourcenode a))"
          using `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `valid_edge a`
          by(fastforce intro:rvI simp:SDG_to_CFG_set_def sourcenodes_def)
        with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
          (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V`
        have "(fst cf\<^sub>1)(outs!i) = (fst cf\<^sub>2)(outs!i)"
          by auto(erule_tac x="0" in allE,auto)
        with 1 2 slice_kind show ?thesis by simp
      next
        case False
        with `transfer (kind a) s\<^sub>1 = s\<^sub>1'`
        have "(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) =
          (fst (hd cfs\<^sub>1))(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs)"
          by(cases cfs\<^sub>1,auto intro:CFG_return_edge_fun)
        show ?thesis
        proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
          case True
          from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
            `(p,ins,outs) \<in> set procs`
          have "slice_kind S a = 
            Q\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. rspp (targetnode a) (HRB_slice S) outs cf' cf)"
            by(rule slice_kind_Return_in_slice)
          with `length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)` 
            `length s\<^sub>1 = length s\<^sub>2`
          have "state_val (transfer (slice_kind S a) s\<^sub>2) V = 
            rspp (targetnode a) (HRB_slice S) outs (fst cfx') (fst cf\<^sub>2) V"
            by simp
          with `V \<notin> set (ParamDefs (targetnode a))`
          have "state_val (transfer (slice_kind S a) s\<^sub>2) V = state_val cfs\<^sub>2 V"
            by(fastforce simp:rspp_def map_merge_def)
          with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
            (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V`
            `hd(tl ms\<^sub>1) = targetnode a`
            `length ms\<^sub>1 = length s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2`[THEN sym] False
            `tl ms\<^sub>2 = tl ms\<^sub>1` `length ms\<^sub>2 = length s\<^sub>2`
            `V\<in>rv S (CFG_node (targetnode a))`
          show ?thesis by(fastforce simp:length_Suc_conv fun_upds_notin)
        next
          case False
          from `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'`
          have "slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')"
            by(rule slice_kind_Return)
          from `length ms\<^sub>2 = length s\<^sub>2` have "1 < length ms\<^sub>2" by simp
          with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
            (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V`
            `V\<in>rv S (CFG_node (hd (tl ms\<^sub>1)))`
            `ms\<^sub>1' = tl ms\<^sub>1` `ms\<^sub>1' = []@hd ms\<^sub>1'#tl ms\<^sub>1'`
          have "fst cfx V = fst cfx' V" apply auto
            apply(erule_tac x="1" in allE)
            by(cases "tl ms\<^sub>1") auto
          with `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
            (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` 
            `hd(tl ms\<^sub>1) = targetnode a`
            `length ms\<^sub>1 = length s\<^sub>1` `length s\<^sub>1 = length s\<^sub>2`[THEN sym] False
            `tl ms\<^sub>2 = tl ms\<^sub>1` `length ms\<^sub>2 = length s\<^sub>2`
            `V\<in>rv S (CFG_node (targetnode a))`
            `V \<notin> set (ParamDefs (targetnode a))`
            `slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')`
          show ?thesis by(auto simp:fun_upds_notin)
        qed
      qed
    qed
    with `hd(tl ms\<^sub>1) = targetnode a` `tl ms\<^sub>2 = tl ms\<^sub>1` `ms\<^sub>1' = tl ms\<^sub>1`
      `\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V` `length ms\<^sub>1' = length s\<^sub>1'`
      `length ms\<^sub>1 = length s\<^sub>1` `length ms\<^sub>2 = length s\<^sub>2` `length s\<^sub>1 = length s\<^sub>2` cf2'
    have "\<forall>i<length ms\<^sub>1'. \<forall>V\<in>rv S (CFG_node ((hd (tl ms\<^sub>1) # tl ms\<^sub>1')!i)).
      (fst (s\<^sub>1'!(length [] + i))) V = (fst (transfer (slice_kind S a) s\<^sub>2!i)) V"
      apply(case_tac "tl ms\<^sub>1") apply auto 
      apply(cases ms\<^sub>2) apply auto
      apply(case_tac i) apply auto
      by(erule_tac x="Suc(Suc nat)" in allE,auto)
    with `\<forall>m \<in> set ms\<^sub>2. valid_node m` `\<forall>m \<in> set ms\<^sub>1'. valid_node m` 
      `length ms\<^sub>2 = length s\<^sub>2` `length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)`
      `length ms\<^sub>1' = length s\<^sub>1'` `ms\<^sub>1' = tl ms\<^sub>1` `ms\<^sub>1' = []@hd ms\<^sub>1'#tl ms\<^sub>1'`
      `tl ms\<^sub>1 = []@hd(tl ms\<^sub>1)#tl(tl ms\<^sub>1)`
      `get_proc mx = get_proc (hd ms\<^sub>2)`
      `\<forall>m \<in> set (tl (tl ms\<^sub>1)). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      `\<forall>m \<in> set (tl (tl ms\<^sub>1)). return_node m`
      `\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)`
    have "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
      by(auto intro!:WSI)
    with `S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)`
    show ?case by blast
  qed
qed



subsection {* The weak simulation *}

definition is_weak_sim :: 
  "(('node list \<times> (('var \<rightharpoonup> 'val) \<times> 'ret) list) \<times> 
  ('node list \<times> (('var \<rightharpoonup> 'val) \<times> 'ret) list)) set \<Rightarrow> 'node SDG_node set \<Rightarrow> bool"
  where "is_weak_sim R S \<equiv> 
  \<forall>ms\<^sub>1 s\<^sub>1 ms\<^sub>2 s\<^sub>2 ms\<^sub>1' s\<^sub>1' as. 
    ((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> R \<and> S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as\<Rightarrow> (ms\<^sub>1',s\<^sub>1') \<and> s\<^sub>1' \<noteq> []
    \<longrightarrow> (\<exists>ms\<^sub>2' s\<^sub>2' as'. ((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>2',s\<^sub>2')) \<in> R \<and> 
                        S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as'\<Rightarrow> (ms\<^sub>2',s\<^sub>2'))"


lemma WS_weak_sim:
  assumes "((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S" 
  and "S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as\<Rightarrow> (ms\<^sub>1',s\<^sub>1')" and "s\<^sub>1' \<noteq> []"
  obtains as' where "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)) \<in> WS S"
  and "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as'@[last as]\<Rightarrow> 
                          (ms\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)"
proof(atomize_elim)
  from `S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as\<Rightarrow> (ms\<^sub>1',s\<^sub>1')` obtain ms' s' as' a'
    where "S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
    and "S,kind \<turnstile> (ms',s') -a'\<rightarrow> (ms\<^sub>1',s\<^sub>1')" and "as = as'@[a']"
    by(fastforce elim:observable_moves.cases)
  from `S,kind \<turnstile> (ms',s') -a'\<rightarrow> (ms\<^sub>1',s\<^sub>1')`
  have "\<forall>m \<in> set (tl ms'). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "\<forall>n \<in> set (tl ms'). return_node n" and "ms' \<noteq> []"
    by(auto elim:observable_move.cases simp:call_of_return_node_def)
  from `S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as'\<Rightarrow>\<^sub>\<tau> (ms',s')` `((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S`
  have "((ms',s'),(ms\<^sub>2,s\<^sub>2)) \<in> WS S" by(rule WS_silent_moves)
  with `S,kind \<turnstile> (ms',s') -a'\<rightarrow> (ms\<^sub>1',s\<^sub>1')` `s\<^sub>1' \<noteq> []`
  obtain as'' where "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a') s\<^sub>2)) \<in> WS S"
    and "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as''@[a']\<Rightarrow> 
    (ms\<^sub>1',transfer (slice_kind S a') s\<^sub>2)"
    by(fastforce elim:WS_observable_move)
  with `((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a') s\<^sub>2)) \<in> WS S` `as = as'@[a']`
  show "\<exists>as'. ((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)) \<in> WS S \<and>
    S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as'@[last as]\<Rightarrow> 
    (ms\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)"
    by fastforce
qed



text {* The following lemma states the correctness of static intraprocedural slicing:\\
  the simulation @{text "WS S"} is a desired weak simulation *}

theorem WS_is_weak_sim:"is_weak_sim (WS S) S"
by(fastforce elim:WS_weak_sim simp:is_weak_sim_def)

end

end

