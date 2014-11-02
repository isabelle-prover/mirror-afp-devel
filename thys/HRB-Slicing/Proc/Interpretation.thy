section {* Instantiate CFG locales with Proc CFG *}

theory Interpretation imports WellFormProgs "../StaticInter/CFGExit" begin

subsection {* Lifting of the basic definitions *}

abbreviation sourcenode :: "edge \<Rightarrow> node"
  where "sourcenode e \<equiv> fst e"

abbreviation targetnode :: "edge \<Rightarrow> node"
  where "targetnode e \<equiv> snd(snd e)"

abbreviation kind :: "edge \<Rightarrow> (vname,val,node,pname) edge_kind"
  where "kind e \<equiv> fst(snd e)"


definition valid_edge :: "wf_prog \<Rightarrow> edge \<Rightarrow> bool"
  where "valid_edge wfp a \<equiv> let (prog,procs) = Rep_wf_prog wfp in
  prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"


definition get_return_edges :: "wf_prog \<Rightarrow> edge \<Rightarrow> edge set"
  where "get_return_edges wfp a \<equiv> 
  case kind a of Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> {a'. valid_edge wfp a' \<and> (\<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f') \<and>
                                 targetnode a' = r}
                     | _ \<Rightarrow> {}"


lemma get_return_edges_non_call_empty:
  "\<forall>Q r p fs. kind a \<noteq> Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Longrightarrow> get_return_edges wfp a = {}"
  by(cases "kind a",auto simp:get_return_edges_def)


lemma call_has_return_edge:
  assumes "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  obtains a' where "valid_edge wfp a'" and "\<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
  and "targetnode a' = r"
proof(atomize_elim)
  from `valid_edge wfp a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  obtain prog procs where "Rep_wf_prog wfp = (prog,procs)"
    and "prog,procs \<turnstile> sourcenode a -Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
    by(fastforce simp:valid_edge_def)
  from `prog,procs \<turnstile> sourcenode a -Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a`
  show "\<exists>a'. valid_edge wfp a' \<and> (\<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f') \<and> targetnode a' = r"
  proof(induct "sourcenode a" "Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" "targetnode a" rule:PCFG.induct)
    case (MainCall l es rets n' ins outs c)
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'` obtain l' 
      where [simp]:"n' = Label l'"
      by(fastforce dest:Proc_CFG_Call_Labels)
    from MainCall
    have "prog,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (Main,Label l'))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs))\<rightarrow> (Main,Label l')"
      by(fastforce intro:MainReturn)
    with `Rep_wf_prog wfp = (prog,procs)` `(Main, n') = r` show ?thesis
      by(fastforce simp:valid_edge_def)
  next
    case (ProcCall px ins outs c l es' rets' l' ins' outs' c' ps)
    from ProcCall have "prog,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (px,Label l'))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets' [:=] map cf outs'))\<rightarrow> (px,Label l')"
      by(fastforce intro:ProcReturn)
    with `Rep_wf_prog wfp = (prog,procs)` `(px, Label l') = r` show ?thesis
      by(fastforce simp:valid_edge_def)
  qed auto
qed


lemma get_return_edges_call_nonempty:
  "\<lbrakk>valid_edge wfp a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> \<Longrightarrow> get_return_edges wfp a \<noteq> {}"
by -(erule call_has_return_edge,(fastforce simp:get_return_edges_def)+)


lemma only_return_edges_in_get_return_edges:
  "\<lbrakk>valid_edge wfp a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges wfp a\<rbrakk>
  \<Longrightarrow> \<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
by(cases "kind a",auto simp:get_return_edges_def)


abbreviation lift_procs :: "wf_prog \<Rightarrow> (pname \<times> vname list \<times> vname list) list"
  where "lift_procs wfp \<equiv> let (prog,procs) = Rep_wf_prog wfp in
  map (\<lambda>x. (fst x,fst(snd x),fst(snd(snd x)))) procs"


subsection {* Instatiation of the @{text CFG} locale *}


interpretation ProcCFG:
  CFG sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main
  for wfp
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastforce simp:wf_prog_def)
  hence wf:"well_formed procs" by(fastforce intro:wf_wf_prog)
  show "CFG sourcenode targetnode kind (valid_edge wfp) (Main, Entry)
    get_proc (get_return_edges wfp) (lift_procs wfp) Main"
  proof
    fix a assume "valid_edge wfp a" and "targetnode a = (Main, Entry)"
    from this wf show False by(auto elim:PCFG.cases simp:valid_edge_def) 
  next
    show "get_proc (Main, Entry) = Main" by simp
  next
    fix a Q r p fs 
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "sourcenode a = (Main, Entry)"
    thus False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    fix a a' 
    assume "valid_edge wfp a" and "valid_edge wfp a'"
      and "sourcenode a = sourcenode a'" and "targetnode a = targetnode a'"
    with wf show "a = a'"
      by(cases a,cases a',auto dest:Proc_CFG_edge_det simp:valid_edge_def)
  next
    fix a Q r f
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>f"
    from this wf show False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    fix a Q' f'
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>Main\<^esub>f'"
    from this wf show False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    fix a Q r p fs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "\<exists>ins outs. (p, ins, outs) \<in> set (lift_procs wfp)"
      apply(auto simp:valid_edge_def) apply(erule PCFG.cases) apply auto
         apply(fastforce dest:Proc_CFG_IEdge_intra_kind simp:intra_kind_def)
        apply(fastforce dest:Proc_CFG_IEdge_intra_kind simp:intra_kind_def)
       apply(rule_tac x="ins" in exI) apply(rule_tac x="outs" in exI)
       apply(rule_tac x="(p,ins,outs,c)" in image_eqI) apply auto
      apply(rule_tac x="ins'" in exI) apply(rule_tac x="outs'" in exI)
      apply(rule_tac x="(p,ins',outs',c')" in image_eqI) by(auto simp:set_conv_nth)
  next
    fix a assume "valid_edge wfp a" and "intra_kind (kind a)"
    thus "get_proc (sourcenode a) = get_proc (targetnode a)"
      by(auto elim:PCFG.cases simp:valid_edge_def intra_kind_def)
  next
    fix a Q r p fs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "get_proc (targetnode a) = p" by(auto elim:PCFG.cases simp:valid_edge_def) 
  next
    fix a Q' p f'
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    thus "get_proc (sourcenode a) = p" by(auto elim:PCFG.cases simp:valid_edge_def) 
  next
    fix a Q r p fs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
    show "\<forall>a'. valid_edge wfp a' \<and> targetnode a' = targetnode a \<longrightarrow>
      (\<exists>Qx rx fsx. kind a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx)"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' ins outs c)
      from `\<lambda>s. True:(Main, n')\<hookrightarrow>\<^bsub>p'\<^esub>map interpret es = kind a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have [simp]:"p' = p" by simp
      { fix a' assume "valid_edge wfp a'" and "targetnode a' = (p', Entry)"
        hence "\<exists>Qx rx fsx. kind a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx"
          by(auto elim:PCFG.cases simp:valid_edge_def) }
      with `(p',Entry) = targetnode a` show ?case by simp
    next
      case (ProcCall px ins outs c l p' es rets l' ins' outs' c' ps)
      from `\<lambda>s. True:(px, Label l')\<hookrightarrow>\<^bsub>p'\<^esub>map interpret es = kind a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have [simp]:"p' = p" by simp
      { fix a' assume "valid_edge wfp a'" and "targetnode a' = (p', Entry)"
        hence "\<exists>Qx rx fsx. kind a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx" 
          by(auto elim:PCFG.cases simp:valid_edge_def) }
      with `(p', Entry) = targetnode a` show ?case by simp
    qed auto
  next
    fix a Q' p f'
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
    show "\<forall>a'. valid_edge wfp a' \<and> sourcenode a' = sourcenode a \<longrightarrow>
      (\<exists>Qx fx. kind a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx)"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainReturn l p' es rets l' ins outs c)
      from `\<lambda>cf. snd cf = (Main, Label l')\<hookleftarrow>\<^bsub>p'\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs) =
        kind a` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have [simp]:"p' = p" by simp
      { fix a' assume "valid_edge wfp a'" and "sourcenode a' = (p', Exit)"
        hence "\<exists>Qx fx. kind a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx" 
          by(auto elim:PCFG.cases simp:valid_edge_def) }
      with `(p', Exit) = sourcenode a` show ?case by simp
    next
      case (ProcReturn px ins outs c l p' es rets l' ins' outs' c' ps)
      from `\<lambda>cf. snd cf = (px, Label l')\<hookleftarrow>\<^bsub>p'\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs') =
        kind a` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have [simp]:"p' = p" by simp
      { fix a' assume "valid_edge wfp a'" and "sourcenode a' = (p', Exit)"
        hence "\<exists>Qx fx. kind a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx" 
          by(auto elim:PCFG.cases simp:valid_edge_def) }
      with `(p', Exit) = sourcenode a` show ?case by simp
    qed auto
  next
    fix a Q r p fs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "get_return_edges wfp a \<noteq> {}" by(rule get_return_edges_call_nonempty)
  next
    fix a a'
    assume "valid_edge wfp a" and "a' \<in> get_return_edges wfp a"
    thus "valid_edge wfp a'"
      by(cases "kind a",auto simp:get_return_edges_def)
  next
    fix a a'
    assume "valid_edge wfp a" and "a' \<in> get_return_edges wfp a"
    thus "\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      by(cases "kind a")(auto simp:get_return_edges_def)
  next
    fix a Q r p fs a'
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "a' \<in> get_return_edges wfp a"
    thus "\<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(rule only_return_edges_in_get_return_edges)
  next
    fix a Q' p f'
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
    show "\<exists>!a'. valid_edge wfp a' \<and> (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
      a \<in> get_return_edges wfp a'"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainReturn l px es rets l' ins outs c)
      from `\<lambda>cf. snd cf = (Main, Label l')\<hookleftarrow>\<^bsub>px\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs) =
        kind a` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have [simp]:"px = p" by simp
      from `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p Label l'` have "l' = Suc l"
        by(fastforce dest:Proc_CFG_Call_Labels)
      from `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p Label l'`
      have "containsCall procs prog [] px" by(rule Proc_CFG_Call_containsCall)
      with `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p Label l'`
        `(px, ins, outs, c) \<in> set procs`        
      have "prog,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (Main,Label l'))\<hookleftarrow>\<^bsub>p\<^esub>
        (\<lambda>cf cf'. cf'(rets [:=] map cf outs))\<rightarrow> (Main,Label l')"
        by(fastforce intro:PCFG.MainReturn)
      with `(px, Exit) = sourcenode a` `(Main, Label l') = targetnode a`
        `\<lambda>cf. snd cf = (Main, Label l')\<hookleftarrow>\<^bsub>px\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs) =
        kind a`
      have edge:"prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a" by simp
      from `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p Label l'`
        `(px, ins, outs, c) \<in> set procs`
      have edge':"prog,procs \<turnstile> (Main,Label l) 
        -(\<lambda>s. True):(Main,Label l')\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es\<rightarrow> (p,Entry)"
        by(fastforce intro:MainCall)
      show ?case
      proof(rule ex_ex1I)
        from edge edge' `(Main, Label l') = targetnode a` 
          `l' = Suc l` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
        show "\<exists>a'. valid_edge wfp a' \<and>
          (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a'"
          by(fastforce simp:valid_edge_def get_return_edges_def)
      next
        fix a' a''
        assume "valid_edge wfp a' \<and>
          (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a'"
          and "valid_edge wfp a'' \<and>
          (\<exists>Q r fs. kind a'' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a''"
        then obtain Q r fs Q' r' fs' where "valid_edge wfp a'"
          and "kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a \<in> get_return_edges wfp a'"
          and "valid_edge wfp a''" and "kind a'' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
          and "a \<in> get_return_edges wfp a''" by blast
        from `valid_edge wfp a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`[THEN sym] edge wf `l' = Suc l`
          `a \<in> get_return_edges wfp a'` `(Main, Label l') = targetnode a`
        have nodes:"sourcenode a' = (Main,Label l) \<and> targetnode a' = (p,Entry)"
          apply(auto simp:valid_edge_def get_return_edges_def)
          by(erule PCFG.cases,auto dest:Proc_CFG_Call_Labels)+
        from `valid_edge wfp a''` `kind a'' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`[THEN sym] `l' = Suc l`
            `a \<in> get_return_edges wfp a''` `(Main, Label l') = targetnode a` wf edge'
        have nodes':"sourcenode a'' = (Main,Label l) \<and> targetnode a'' = (p,Entry)"
          apply(auto simp:valid_edge_def get_return_edges_def)
          by(erule PCFG.cases,auto dest:Proc_CFG_Call_Labels)+
        with nodes `valid_edge wfp a'` `valid_edge wfp a''` wf
        have "kind a' = kind a''"
          by(fastforce dest:Proc_CFG_edge_det simp:valid_edge_def)
        with nodes nodes' show "a' = a''" by(cases a',cases a'',auto)
      qed
    next
      case (ProcReturn p' ins outs c l px esx retsx l' ins' outs' c' ps)
      from `\<lambda>cf. snd cf = (p', Label l')\<hookleftarrow>\<^bsub>px\<^esub>\<lambda>cf cf'. cf'(retsx [:=] map cf outs') =
        kind a` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have [simp]:"px = p" by simp
      from `c \<turnstile> Label l -CEdge (px, esx, retsx)\<rightarrow>\<^sub>p Label l'` have "l' = Suc l"
        by(fastforce dest:Proc_CFG_Call_Labels)
      from `(p',ins,outs,c) \<in> set procs`
        `c \<turnstile> Label l -CEdge (px, esx, retsx)\<rightarrow>\<^sub>p Label l'` 
        `(px, ins', outs', c') \<in> set procs` `containsCall procs prog ps p'`
      have "prog,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (p',Label l'))\<hookleftarrow>\<^bsub>p\<^esub>
        (\<lambda>cf cf'. cf'(retsx [:=] map cf outs'))\<rightarrow> (p',Label l')"
        by(fastforce intro:PCFG.ProcReturn)
      with `(px, Exit) = sourcenode a` `(p', Label l') = targetnode a`
        `\<lambda>cf. snd cf = (p', Label l')\<hookleftarrow>\<^bsub>px\<^esub>\<lambda>cf cf'. cf'(retsx [:=] map cf outs') =
        kind a` have edge:"prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a" by simp
      from `(p',ins,outs,c) \<in> set procs`
        `c \<turnstile> Label l -CEdge (px, esx, retsx)\<rightarrow>\<^sub>p Label l'`
        `(px, ins', outs', c') \<in> set procs` `containsCall procs prog ps p'`
      have edge':"prog,procs \<turnstile> (p',Label l) 
        -(\<lambda>s. True):(p',Label l')\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) esx\<rightarrow> (p,Entry)"
        by(fastforce intro:ProcCall)
      show ?case
      proof(rule ex_ex1I)
        from edge edge' `(p', Label l') = targetnode a` `l' = Suc l`
          `(p', ins, outs, c) \<in> set procs` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
        show "\<exists>a'. valid_edge wfp a' \<and>
          (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a'"
          by(fastforce simp:valid_edge_def get_return_edges_def)
      next
        fix a' a''
        assume "valid_edge wfp a' \<and>
          (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a'"
          and "valid_edge wfp a'' \<and>
          (\<exists>Q r fs. kind a'' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a''"
        then obtain Q r fs Q' r' fs' where "valid_edge wfp a'"
          and "kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a \<in> get_return_edges wfp a'"
          and "valid_edge wfp a''" and "kind a'' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
          and "a \<in> get_return_edges wfp a''" by blast
        from `valid_edge wfp a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`[THEN sym] 
          `a \<in> get_return_edges wfp a'` edge `(p', Label l') = targetnode a` wf
          `(p', ins, outs, c) \<in> set procs` `l' = Suc l`
        have nodes:"sourcenode a' = (p',Label l) \<and> targetnode a' = (p,Entry)"
          apply(auto simp:valid_edge_def get_return_edges_def)
          by(erule PCFG.cases,auto dest:Proc_CFG_Call_Labels)+
        from `valid_edge wfp a''` `kind a'' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`[THEN sym] 
          `a \<in> get_return_edges wfp a''` edge `(p', Label l') = targetnode a` wf
          `(p', ins, outs, c) \<in> set procs` `l' = Suc l`
        have nodes':"sourcenode a'' = (p',Label l) \<and> targetnode a'' = (p,Entry)"
          apply(auto simp:valid_edge_def get_return_edges_def)
          by(erule PCFG.cases,auto dest:Proc_CFG_Call_Labels)+
        with nodes `valid_edge wfp a'` `valid_edge wfp a''` wf
        have "kind a' = kind a''"
          by(fastforce dest:Proc_CFG_edge_det simp:valid_edge_def)
        with nodes nodes' show "a' = a''" by(cases a',cases a'',auto)
      qed
    qed auto
  next
    fix a a'
    assume "valid_edge wfp a" and "a' \<in> get_return_edges wfp a"
    then obtain Q r p fs l'
      where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "valid_edge wfp a'"
      by(cases "kind a")(fastforce simp:valid_edge_def get_return_edges_def)+
    from `valid_edge wfp a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges wfp a`
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" 
      by(fastforce dest!:only_return_edges_in_get_return_edges)
    with `valid_edge wfp a'` have "sourcenode a' = (p,Exit)"
      by(auto elim:PCFG.cases simp:valid_edge_def)
    from `valid_edge wfp a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "prog,procs \<turnstile> sourcenode a -Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    thus "\<exists>a''. valid_edge wfp a'' \<and> sourcenode a'' = targetnode a \<and> 
      targetnode a'' = sourcenode a' \<and> kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    proof(induct "sourcenode a" "Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" "targetnode a" rule:PCFG.induct)
      case (MainCall l es rets n' ins outs c)
      have "c \<turnstile> Entry -IEdge (\<lambda>s. False)\<^sub>\<surd>\<rightarrow>\<^sub>p Exit" by(rule Proc_CFG_Entry_Exit)
      moreover
      from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
      have "containsCall procs prog [] p" by(rule Proc_CFG_Call_containsCall)
      ultimately have "prog,procs \<turnstile> (p,Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (p,Exit)"
        using `(p, ins, outs, c) \<in> set procs` by(fastforce intro:Proc)
      with `sourcenode a' = (p,Exit)` `(p, Entry) = targetnode a`[THEN sym]
      show ?case by(fastforce simp:valid_edge_def)
    next
      case (ProcCall px ins outs c l es' rets' l' ins' outs' c' ps)
      have "c' \<turnstile> Entry -IEdge (\<lambda>s. False)\<^sub>\<surd>\<rightarrow>\<^sub>p Exit" by(rule Proc_CFG_Entry_Exit)
      moreover
      from `c \<turnstile> Label l -CEdge (p, es', rets')\<rightarrow>\<^sub>p Label l'`
      have "containsCall procs c [] p" by(rule Proc_CFG_Call_containsCall)
      with `containsCall procs prog ps px` `(px,ins,outs,c) \<in> set procs`
      have "containsCall procs prog (ps@[px]) p"
        by(rule containsCall_in_proc)
      ultimately have "prog,procs \<turnstile> (p,Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (p,Exit)"
        using `(p, ins', outs', c') \<in> set procs` by(fastforce intro:Proc)
      with `sourcenode a' = (p,Exit)` `(p, Entry) = targetnode a`[THEN sym]
      show ?case by(fastforce simp:valid_edge_def)
    qed auto
  next
    fix a a'
    assume "valid_edge wfp a" and "a' \<in> get_return_edges wfp a"
    then obtain Q r p fs l'
      where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "valid_edge wfp a'"
      by(cases "kind a")(fastforce simp:valid_edge_def get_return_edges_def)+
    from `valid_edge wfp a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges wfp a`
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" and "targetnode a' = r"
      by(auto simp:get_return_edges_def)
    from `valid_edge wfp a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "prog,procs \<turnstile> sourcenode a -Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    thus "\<exists>a''. valid_edge wfp a'' \<and> sourcenode a'' = sourcenode a \<and> 
      targetnode a'' = targetnode a' \<and> kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    proof(induct "sourcenode a" "Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" "targetnode a" rule:PCFG.induct)
      case (MainCall l es rets n' ins outs c)
      from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
      have "prog,procs \<turnstile> (Main,Label l) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,n')"
        by(rule MainCallReturn)
      with `(Main, Label l) = sourcenode a`[THEN sym] `targetnode a' = r`
        `(Main, n') = r`[THEN sym]
      show ?case by(auto simp:valid_edge_def)
    next
      case (ProcCall px ins outs c l es' rets' l' ins' outs' c' ps)
      from `(px,ins,outs,c) \<in> set procs`         `containsCall procs prog ps px`
        `c \<turnstile> Label l -CEdge (p, es', rets')\<rightarrow>\<^sub>p Label l'`
      have "prog,procs \<turnstile> (px,Label l) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (px,Label l')"
        by(fastforce intro:ProcCallReturn)
      with `(px, Label l) = sourcenode a`[THEN sym] `targetnode a' = r`
        `(px, Label l') = r`[THEN sym]
      show ?case by(auto simp:valid_edge_def)
    qed auto
  next
    fix a Q r p fs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
    show "\<exists>!a'. valid_edge wfp a' \<and>
      sourcenode a' = sourcenode a \<and> intra_kind (kind a')"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' ins outs c)
      show ?thesis 
      proof(rule ex_ex1I)
        from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
        have "prog,procs \<turnstile> (Main,Label l) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,n')"
          by(rule MainCallReturn)
        with `(Main, Label l) = sourcenode a`[THEN sym]
        show "\<exists>a'. valid_edge wfp a' \<and>
          sourcenode a' = sourcenode a \<and> intra_kind (kind a')"
          by(fastforce simp:valid_edge_def intra_kind_def) 
      next
        fix a' a'' 
        assume "valid_edge wfp a' \<and> sourcenode a' = sourcenode a \<and> 
          intra_kind (kind a')" and "valid_edge wfp a'' \<and>
          sourcenode a'' = sourcenode a \<and> intra_kind (kind a'')"
        hence "valid_edge wfp a'" and "sourcenode a' = sourcenode a"
          and "intra_kind (kind a')" and "valid_edge wfp a''"
          and "sourcenode a'' = sourcenode a" and "intra_kind (kind a'')" by simp_all
        from `valid_edge wfp a'` `sourcenode a' = sourcenode a`
          `intra_kind (kind a')` `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
          `(Main, Label l) = sourcenode a` wf
        have "targetnode a' = (Main,Label (Suc l))"
          by(auto elim!:PCFG.cases dest:Proc_CFG_Call_Intra_edge_not_same_source 
            Proc_CFG_Call_Labels simp:intra_kind_def valid_edge_def)
        from `valid_edge wfp a''` `sourcenode a'' = sourcenode a`
          `intra_kind (kind a'')` `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
          `(Main, Label l) = sourcenode a` wf
        have "targetnode a'' = (Main,Label (Suc l))"
          by(auto elim!:PCFG.cases dest:Proc_CFG_Call_Intra_edge_not_same_source 
            Proc_CFG_Call_Labels simp:intra_kind_def valid_edge_def)
        with `valid_edge wfp a'` `sourcenode a' = sourcenode a`
          `valid_edge wfp a''` `sourcenode a'' = sourcenode a`
          `targetnode a' = (Main,Label (Suc l))` wf
        show "a' = a''" by(cases a',cases a'')
        (auto dest:Proc_CFG_edge_det simp:valid_edge_def)
      qed
    next
      case (ProcCall px ins outs c l p' es' rets' l' ins' outs' c' ps)
      show ?thesis 
      proof(rule ex_ex1I)
        from `(px, ins, outs, c) \<in> set procs` `containsCall procs prog ps px`
          `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
        have "prog,procs \<turnstile> (px,Label l) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (px,Label l')"
          by -(rule ProcCallReturn)
        with `(px, Label l) = sourcenode a`[THEN sym]
        show "\<exists>a'. valid_edge wfp a' \<and> sourcenode a' = sourcenode a \<and> 
                   intra_kind (kind a')"
          by(fastforce simp:valid_edge_def intra_kind_def)
      next
        fix a' a'' 
        assume "valid_edge wfp a' \<and> sourcenode a' = sourcenode a \<and> 
          intra_kind (kind a')" and "valid_edge wfp a'' \<and>
          sourcenode a'' = sourcenode a \<and> intra_kind (kind a'')"
        hence "valid_edge wfp a'" and "sourcenode a' = sourcenode a"
          and "intra_kind (kind a')" and "valid_edge wfp a''"
          and "sourcenode a'' = sourcenode a" and "intra_kind (kind a'')" by simp_all
        from `valid_edge wfp a'` `sourcenode a' = sourcenode a`
          `intra_kind (kind a')` `(px, ins, outs, c) \<in> set procs`
          `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
          `(p', ins', outs', c') \<in> set procs` wf
          `containsCall procs prog ps px` `(px, Label l) = sourcenode a`
        have "targetnode a' = (px,Label (Suc l))"
          apply(auto simp:valid_edge_def) apply(erule PCFG.cases)
          by(auto dest:Proc_CFG_Call_Intra_edge_not_same_source 
            Proc_CFG_Call_nodes_eq Proc_CFG_Call_Labels simp:intra_kind_def)
        from `valid_edge wfp a''` `sourcenode a'' = sourcenode a`
          `intra_kind (kind a'')` `(px, ins, outs, c) \<in> set procs`
          `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
          `(p', ins', outs', c') \<in> set procs` wf
          `containsCall procs prog ps px` `(px, Label l) = sourcenode a`
        have "targetnode a'' = (px,Label (Suc l))"
          apply(auto simp:valid_edge_def) apply(erule PCFG.cases)
          by(auto dest:Proc_CFG_Call_Intra_edge_not_same_source 
            Proc_CFG_Call_nodes_eq Proc_CFG_Call_Labels simp:intra_kind_def)
        with `valid_edge wfp a'` `sourcenode a' = sourcenode a`
          `valid_edge wfp a''` `sourcenode a'' = sourcenode a`
          `targetnode a' = (px,Label (Suc l))` wf
        show "a' = a''" by(cases a',cases a'')
        (auto dest:Proc_CFG_edge_det simp:valid_edge_def)
      qed
    qed auto
  next
    fix a Q' p f'
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
    show "\<exists>!a'. valid_edge wfp a' \<and>
      targetnode a' = targetnode a \<and> intra_kind (kind a')"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainReturn l p' es rets l' ins outs c)
      show ?thesis 
      proof(rule ex_ex1I)
        from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
        have "prog,procs \<turnstile> (Main,Label l) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> 
          (Main,Label l')" by(rule MainCallReturn)
        with `(Main, Label l') = targetnode a`[THEN sym]
        show "\<exists>a'. valid_edge wfp a' \<and>
          targetnode a' = targetnode a \<and> intra_kind (kind a')"
          by(fastforce simp:valid_edge_def intra_kind_def)
      next
        fix a' a''
        assume "valid_edge wfp a' \<and> targetnode a' = targetnode a \<and> 
          intra_kind (kind a')" and "valid_edge wfp a'' \<and>
          targetnode a'' = targetnode a \<and> intra_kind (kind a'')"
        hence "valid_edge wfp a'" and "targetnode a' = targetnode a"
          and "intra_kind (kind a')" and "valid_edge wfp a''"
          and "targetnode a'' = targetnode a" and "intra_kind (kind a'')" by simp_all
        from `valid_edge wfp a'` `targetnode a' = targetnode a`
          `intra_kind (kind a')` `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
          `(Main, Label l') = targetnode a` wf
        have "sourcenode a' = (Main,Label l)"
          apply(auto elim!:PCFG.cases dest:Proc_CFG_Call_Intra_edge_not_same_target 
                      simp:valid_edge_def intra_kind_def)
          by(fastforce dest:Proc_CFG_Call_nodes_eq' Proc_CFG_Call_Labels)
        from `valid_edge wfp a''` `targetnode a'' = targetnode a`
          `intra_kind (kind a'')` `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
          `(Main, Label l') = targetnode a` wf
        have "sourcenode a'' = (Main,Label l)"
          apply(auto elim!:PCFG.cases dest:Proc_CFG_Call_Intra_edge_not_same_target 
                      simp:valid_edge_def intra_kind_def)
          by(fastforce dest:Proc_CFG_Call_nodes_eq' Proc_CFG_Call_Labels)
        with `valid_edge wfp a'` `targetnode a' = targetnode a`
          `valid_edge wfp a''` `targetnode a'' = targetnode a`
          `sourcenode a' = (Main,Label l)` wf
        show "a' = a''" by(cases a',cases a'')
        (auto dest:Proc_CFG_edge_det simp:valid_edge_def)
      qed
    next
      case (ProcReturn px ins outs c l p' es' rets' l' ins' outs' c' ps)
      show ?thesis 
      proof(rule ex_ex1I)
        from `(px, ins, outs, c) \<in> set procs` `containsCall procs prog ps px`
          `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
        have "prog,procs \<turnstile> (px,Label l) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (px,Label l')"
          by -(rule ProcCallReturn)
        with `(px, Label l') = targetnode a`[THEN sym]
        show "\<exists>a'. valid_edge wfp a' \<and>
          targetnode a' = targetnode a \<and> intra_kind (kind a')"
          by(fastforce simp:valid_edge_def intra_kind_def)
      next
        fix a' a''
        assume "valid_edge wfp a' \<and> targetnode a' = targetnode a \<and> 
          intra_kind (kind a')" and "valid_edge wfp a'' \<and>
          targetnode a'' = targetnode a \<and> intra_kind (kind a'')"
        hence "valid_edge wfp a'" and "targetnode a' = targetnode a"
          and "intra_kind (kind a')" and "valid_edge wfp a''"
          and "targetnode a'' = targetnode a" and "intra_kind (kind a'')" by simp_all
        from `valid_edge wfp a'` `targetnode a' = targetnode a`
          `intra_kind (kind a')` `(px, ins, outs, c) \<in> set procs`
          `(p', ins', outs', c') \<in> set procs` wf
          `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
          `containsCall procs prog ps px` `(px, Label l') = targetnode a`
        have "sourcenode a' = (px,Label l)"
          apply(auto simp:valid_edge_def) apply(erule PCFG.cases)
          by(auto dest:Proc_CFG_Call_Intra_edge_not_same_target 
            Proc_CFG_Call_nodes_eq' simp:intra_kind_def)
        from `valid_edge wfp a''` `targetnode a'' = targetnode a`
          `intra_kind (kind a'')` `(px, ins, outs, c) \<in> set procs`
          `(p', ins', outs', c') \<in> set procs` wf
          `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
          `containsCall procs prog ps px` `(px, Label l') = targetnode a`
        have "sourcenode a'' = (px,Label l)"
          apply(auto simp:valid_edge_def) apply(erule PCFG.cases)
          by(auto dest:Proc_CFG_Call_Intra_edge_not_same_target 
            Proc_CFG_Call_nodes_eq' simp:intra_kind_def)
        with `valid_edge wfp a'` `targetnode a' = targetnode a`
          `valid_edge wfp a''` `targetnode a'' = targetnode a`
          `sourcenode a' = (px,Label l)` wf
        show "a' = a''" by(cases a',cases a'')
        (auto dest:Proc_CFG_edge_det simp:valid_edge_def)
      qed
    qed auto
  next
    fix a a' Q\<^sub>1 r\<^sub>1 p fs\<^sub>1 Q\<^sub>2 r\<^sub>2 fs\<^sub>2
    assume "valid_edge wfp a" and "valid_edge wfp a'"
      and "kind a = Q\<^sub>1:r\<^sub>1\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>1" and "kind a' = Q\<^sub>2:r\<^sub>2\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>2"
    thus "targetnode a = targetnode a'" by(auto elim!:PCFG.cases simp:valid_edge_def)
  next
    from wf show "distinct_fst (lift_procs wfp)"
      by(fastforce simp:well_formed_def distinct_fst_def o_def)
  next
    fix p ins outs assume "(p, ins, outs) \<in> set (lift_procs wfp)"
    from `(p, ins, outs) \<in> set (lift_procs wfp)` wf
    show "distinct ins" by(fastforce simp:well_formed_def wf_proc_def)
  next
    fix p ins outs assume "(p, ins, outs) \<in> set (lift_procs wfp)"
    from `(p, ins, outs) \<in> set (lift_procs wfp)` wf
    show "distinct outs" by(fastforce simp:well_formed_def wf_proc_def)
  qed
qed



subsection {* Instatiation of the @{text CFGExit} locale *}


interpretation ProcCFGExit:
  CFGExit sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main "(Main,Exit)"
  for wfp
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastforce simp:wf_prog_def)
  hence wf:"well_formed procs" by(fastforce intro:wf_wf_prog)
  show "CFGExit sourcenode targetnode kind (valid_edge wfp) (Main, Entry)
    get_proc (get_return_edges wfp) (lift_procs wfp) Main (Main, Exit)"
  proof
    fix a assume "valid_edge wfp a" and "sourcenode a = (Main, Exit)"
    with wf show False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    show "get_proc (Main, Exit) = Main" by simp
  next
    fix a Q p f
    assume "valid_edge wfp a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      and "targetnode a = (Main, Exit)"
    thus False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    have "prog,procs \<turnstile> (Main,Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,Exit)"
      by(fastforce intro:Main Proc_CFG_Entry_Exit)
    thus "\<exists>a. valid_edge wfp a \<and>
      sourcenode a = (Main, Entry) \<and>
      targetnode a = (Main, Exit) \<and> kind a = (\<lambda>s. False)\<^sub>\<surd>"
      by(fastforce simp:valid_edge_def)
  qed
qed


end