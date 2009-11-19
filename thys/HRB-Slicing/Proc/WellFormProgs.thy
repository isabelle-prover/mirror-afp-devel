header {* \isaheader{Well-formedness of programs} *}

theory WellFormProgs imports PCFG begin

subsection {* Well-formedness of procedure lists. *}

definition wf_proc :: "proc \<Rightarrow> bool"
  where "wf_proc x \<equiv> let (p,ins,outs,c) = x in 
  p \<noteq> Main \<and> length ins \<ge> 2 \<and> hd ins = ReturnProc \<and> hd(tl ins) = ReturnLabel \<and>
  distinct ins \<and> distinct outs \<and> 
  (\<forall>out \<in> set outs. out \<noteq> ReturnProc \<and> out \<noteq> ReturnLabel)"

definition well_formed :: "procs \<Rightarrow> bool"
  where "well_formed procs \<equiv> distinct_fst procs \<and> 
  (\<forall>(p,ins,outs,c) \<in> set procs. wf_proc (p,ins,outs,c))"

lemma [dest]:"\<lbrakk>well_formed procs; (Main,ins,outs,c) \<in> set procs\<rbrakk> \<Longrightarrow> False"
  by(fastsimp simp:well_formed_def wf_proc_def)

lemma [dest]:"\<lbrakk>well_formed procs; i < length procs; procs!i = (Main,ins,outs,c)\<rbrakk>
  \<Longrightarrow> False"
  by(fastsimp dest:nth_mem)

lemma well_formed_same_procs [dest]:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs; (p,ins',outs',c') \<in> set procs\<rbrakk>
  \<Longrightarrow> ins = ins' \<and> outs = outs' \<and> c = c'"
  apply(auto simp:well_formed_def distinct_fst_def distinct_map inj_on_def)
by(erule_tac x="(p,ins,outs,c)" in ballE,auto)+

lemma well_formed_same_procs_nth [dest]:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs; i < length procs;
    procs!i = (p,ins',outs',c')\<rbrakk> 
  \<Longrightarrow> ins = ins' \<and> outs = outs' \<and> c = c'"
  by(fastsimp dest:nth_mem)

lemma well_formed_same_procs_nth_nth:
  "\<lbrakk>well_formed procs; i < length procs; j < length procs; procs!i = (p,ins,outs,c);
    procs!j = (p,ins',outs',c')\<rbrakk>
  \<Longrightarrow> ins = ins' \<and> outs = outs' \<and> c = c' \<and> i = j"
  by(fastsimp simp:well_formed_def distinct_fst_def distinct_map distinct_conv_nth)



lemma PCFG_sourcelabel_None_less_num_nodes:
  "\<lbrakk>prog,procs \<turnstile> (Main,Label l) -et\<rightarrow> n'; well_formed procs\<rbrakk> \<Longrightarrow> l < #:prog"
proof(induct n\<equiv>"(Main,Label l)" et n' 
      arbitrary:l rule:PCFG.induct)
  case (Main n et n')
  from `prog \<turnstile> n -IEdge et\<rightarrow>\<^isub>p n'` `(Main,n) = (Main,Label l)`
  show ?case by(fastsimp elim:Proc_CFG_sourcelabel_less_num_nodes)
next
  case (MainCall l' p es rets n' ins outs c)
  from `prog \<turnstile> Label l' -CEdge (p,es,rets)\<rightarrow>\<^isub>p n'` `(Main,Label l') = (Main,Label l)`
  show ?case by(fastsimp elim:Proc_CFG_sourcelabel_less_num_nodes)
next
  case (MainCallReturn n p es rets n' l)
  from `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'` `(Main, n) = (Main, Label l)`
  show ?case by(fastsimp elim:Proc_CFG_sourcelabel_less_num_nodes)
qed auto

lemma Proc_CFG_sourcelabel_Some_less_num_nodes:
  "\<lbrakk>prog,procs \<turnstile> (p,Label l) -et\<rightarrow> n'; (p,ins,outs,c) \<in> set procs; 
    well_formed procs\<rbrakk> \<Longrightarrow> l < #:c"
proof(induct n\<equiv>"(p,Label l)" et n' arbitrary:l rule:PCFG.induct)
  case (Proc p' ins' outs' c' n et n')
  from `(p',n) = (p,Label l)` have "p = p'" and "n = Label l" by simp+
  from `c' \<turnstile> n -IEdge et\<rightarrow>\<^isub>p n'` `n = Label l` have "l < #:c'"
    by(fastsimp intro:Proc_CFG_sourcelabel_less_num_nodes)
  with `well_formed procs` `p = p'` `(p,ins,outs,c) \<in> set procs` 
    `(p',ins',outs',c') \<in> set procs`
  show ?case by fastsimp
next
  case (ProcCall i p' ins' outs' c' l' p'' es rets l'' ins'' outs'' c'')
  from `(p',Label l') = (p,Label l)` have "p = p'" and "l' = l" by simp_all
  from `c' \<turnstile> Label l' -CEdge (p'',es,rets)\<rightarrow>\<^isub>p Label l''` `l' = l` have "l < #:c'"
    by(fastsimp intro:Proc_CFG_sourcelabel_less_num_nodes)
  with `well_formed procs` `p = p'` `(p,ins,outs,c) \<in> set procs` 
    `i < length procs` `procs ! i = (p', ins', outs', c')`
  show ?case by fastsimp
next
  case (ProcCallReturn p' ins' outs' c' n p'' es rets n')
  from `(p',n) = (p,Label l)` have "p = p'" and "n = Label l" by simp+
  from `c' \<turnstile> n -CEdge (p'', es, rets)\<rightarrow>\<^isub>p n'` `n = Label l` have "l < #:c'"
    by(fastsimp intro:Proc_CFG_sourcelabel_less_num_nodes)
  with `well_formed procs` `p = p'` `(p,ins,outs,c) \<in> set procs` 
    `(p',ins',outs',c') \<in> set procs`
  show ?case by fastsimp
qed auto


lemma Proc_CFG_targetlabel_Main_less_num_nodes:
  "\<lbrakk>prog,procs \<turnstile> n -et\<rightarrow> (Main,Label l); well_formed procs\<rbrakk> \<Longrightarrow> l < #:prog"
proof(induct n et n'\<equiv>"(Main,Label l)" 
      arbitrary:l rule:PCFG.induct)
  case (Main n et n')
  from `prog \<turnstile> n -IEdge et\<rightarrow>\<^isub>p n'` `(Main, n') = (Main, Label l)`
  show ?case by(fastsimp elim:Proc_CFG_targetlabel_less_num_nodes)
next
  case (MainReturn l' p es rets l'' ins outs c)
  from `prog \<turnstile> Label l' -CEdge (p,es,rets)\<rightarrow>\<^isub>p Label l''` 
    `(Main,Label l'') = (Main,Label l)`
  show ?case by(fastsimp elim:Proc_CFG_targetlabel_less_num_nodes)
next
  case (MainCallReturn n p es rets n' l)
  from `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'` `(Main, n') = (Main, Label l)`
  show ?case by(fastsimp elim:Proc_CFG_targetlabel_less_num_nodes)
qed auto


lemma Proc_CFG_targetlabel_Some_less_num_nodes:
  "\<lbrakk>prog,procs \<turnstile> n -et\<rightarrow> (p,Label l); (p,ins,outs,c) \<in> set procs; 
    well_formed procs\<rbrakk> \<Longrightarrow> l < #:c"
proof(induct n et n'\<equiv>"(p,Label l)" arbitrary:l rule:PCFG.induct)
  case (Proc p' ins' outs' c' n et n')
  from `(p', n') = (p, Label l)` have "p = p'" and "n' = Label l" by simp_all
  from `c' \<turnstile> n -IEdge et\<rightarrow>\<^isub>p n'` `n' = Label l` have "l < #:c'"
    by(fastsimp intro:Proc_CFG_targetlabel_less_num_nodes)
  with `well_formed procs` `p = p'` `(p,ins,outs,c) \<in> set procs` 
    `(p',ins',outs',c') \<in> set procs`
  show ?case by fastsimp
next
  case (ProcReturn i p' ins' outs' c' l' p'' es rets l'' ins'' outs'' c'')
  from `(p',Label l'') = (p,Label l)` have "p = p'" and "l'' = l" by simp_all
  from `c' \<turnstile> Label l' -CEdge (p'',es,rets)\<rightarrow>\<^isub>p Label l''` `l'' = l` have "l < #:c'"
    by(fastsimp intro:Proc_CFG_targetlabel_less_num_nodes)
  with `well_formed procs` `p = p'` `(p,ins,outs,c) \<in> set procs` 
    `i < length procs` `procs ! i = (p', ins', outs', c')`
  show ?case by fastsimp
next
  case (ProcCallReturn p' ins' outs' c' n p'' es rets n')
  from `(p',n') = (p,Label l)` have "p = p'" and "n' = Label l" by simp+
  from `c' \<turnstile> n -CEdge (p'', es, rets)\<rightarrow>\<^isub>p n'` `n' = Label l` have "l < #:c'"
    by(fastsimp intro:Proc_CFG_targetlabel_less_num_nodes)
  with `well_formed procs` `p = p'` `(p,ins,outs,c) \<in> set procs` 
    `(p',ins',outs',c') \<in> set procs`
  show ?case by fastsimp
qed auto


lemma Proc_CFG_edge_det:
  "\<lbrakk>prog,procs \<turnstile> n -et\<rightarrow> n'; prog,procs \<turnstile> n -et'\<rightarrow> n'; well_formed procs\<rbrakk>
  \<Longrightarrow> et = et'"
proof(induct rule:PCFG.induct)
  case Main thus ?case by(auto elim:PCFG.cases dest:Proc_CFG_edge_det)
next
  case Proc thus ?case by(auto elim:PCFG.cases dest:Proc_CFG_edge_det)
next
  case (MainCall l p es rets n' ins outs c)
  from `prog,procs \<turnstile> (Main,Label l) -et'\<rightarrow> (p,Entry)` `well_formed procs`
  obtain es' rets' n'' ins' outs' c' 
    where "prog \<turnstile> Label l -CEdge (p,es',rets')\<rightarrow>\<^isub>p n''" 
    and "(p,ins',outs',c') \<in> set procs" 
    and "et' = (\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc l) es'"
    by(auto elim:PCFG.cases)
  from `(p,ins,outs,c) \<in> set procs` `(p,ins',outs',c') \<in> set procs`
    `well_formed procs`
  have "ins = ins'" by fastsimp
  from `prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^isub>p n'`
    `prog \<turnstile> Label l -CEdge (p,es',rets')\<rightarrow>\<^isub>p n''`
  have "es = es'" and "n' = n''" by(auto dest:Proc_CFG_Call_nodes_eq)
  with `et' = (\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc l) es'` `ins = ins'`
  show ?case by simp
next
  case (ProcCall i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
  from `prog,procs \<turnstile> (p,Label l) -et'\<rightarrow> (p',Entry)`
    `(p',ins',outs',c') \<in> set procs` `well_formed procs`
    `i < length procs` `procs ! i = (p, ins, outs, c)` `well_formed procs`
    `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
  show ?case
  proof(induct n\<equiv>"(p,Label l)" et' n'\<equiv>"(p',Entry)" rule:PCFG.induct)
    case (ProcCall ix px insx outsx cx lx p'x es'x rets'x l'x ins'x outs'x c'x 
      esx retsx)
    from `(p'x, Entry) = (p', Entry)` have [simp]:"p'x = p'" by simp
    from `(px, Label lx) = (p, Label l)` have [simp]:"lx = l" "px = p" by simp_all
    from `well_formed procs` `ix < length procs` `i < length procs` 
      `procs ! ix = (px, insx, outsx, cx)` `procs ! i = (p, ins, outs, c)`
    have [simp]:"ix = i" "cx = c" by(auto dest:well_formed_same_procs_nth_nth)
    from `cx \<turnstile> Label lx -CEdge (p'x, es'x, rets'x)\<rightarrow>\<^isub>p Label l'x`
      `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
    have [simp]:"es'x = es'" by(fastsimp dest:Proc_CFG_Call_nodes_eq)
    show ?case by simp
  qed auto
next
  case MainReturn
  thus ?case by -(erule PCFG.cases,auto dest:Proc_CFG_Call_nodes_eq')
next
  case (ProcReturn i p ins outs c l p' es' rets' l' ins' outs' c' ps es rets)
  from `prog,procs \<turnstile> (p',Exit) -et'\<rightarrow> (p, Label l')`
    `i < length procs` `procs ! i = (p, ins, outs, c)`
    `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'` 
    `(p', ins', outs', c') \<in> set procs`
    `containsCall procs prog ps p es rets` `well_formed procs`
  show ?case
  proof(induct n\<equiv>"(p',Exit)" et' n'\<equiv>"(p,Label l')" rule:PCFG.induct)
    case (ProcReturn ix px insx outsx cx lx p'x es'x rets'x l'x ins'x outs'x c'x psx
      esx retsx)
    from `(p'x, Exit) = (p', Exit)` have [simp]:"p'x = p'" by simp
    with `(p'x, ins'x, outs'x, c'x) \<in> set procs`
      `(p', ins', outs', c') \<in> set procs` `well_formed procs`
    have [simp]:"outs'x = outs'" by fastsimp
    from `(px, Label l'x) = (p, Label l')` have [simp]:"px = p" "l'x = l'" by simp_all
    from `ix < length procs` `procs ! ix = (px, insx, outsx, cx)`
      `i < length procs` `procs ! i = (p, ins, outs, c)` `well_formed procs`
    have [simp]:"ix = i" "cx = c" by(auto dest:well_formed_same_procs_nth_nth)
    from `cx \<turnstile> Label lx -CEdge (p'x, es'x, rets'x)\<rightarrow>\<^isub>p Label l'x`
      `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
    have [simp]:"rets'x = rets'" by(fastsimp dest:Proc_CFG_Call_nodes_eq')
    show ?case by simp
  qed auto
next
  case MainCallReturn thus ?case by(auto elim:PCFG.cases dest:Proc_CFG_edge_det)
next
  case ProcCallReturn thus ?case by(auto elim:PCFG.cases dest:Proc_CFG_edge_det)
qed


lemma Proc_CFG_deterministic:
  "\<lbrakk>prog,procs \<turnstile> n\<^isub>1 -et\<^isub>1\<rightarrow> n\<^isub>1'; prog,procs \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n\<^isub>1 = n\<^isub>2; n\<^isub>1' \<noteq> n\<^isub>2'; 
   intra_kind et\<^isub>1; intra_kind et\<^isub>2; well_formed procs\<rbrakk>
  \<Longrightarrow> \<exists>Q Q'. et\<^isub>1 = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> 
            (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
proof(induct arbitrary:n\<^isub>2 n\<^isub>2' rule:PCFG.induct)
  case (Main n et n')
  from `prog,procs \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(Main,n) = n\<^isub>2`
    `intra_kind et\<^isub>2` `well_formed procs`
  obtain m m' where "(Main,m) = n\<^isub>2" and "(Main,m') = n\<^isub>2'"
    and disj:"prog \<turnstile> m -IEdge et\<^isub>2\<rightarrow>\<^isub>p m' \<or> 
    (\<exists>p es rets. prog \<turnstile> m -CEdge (p,es,rets)\<rightarrow>\<^isub>p m' \<and> et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>)"
    by(induct rule:PCFG.induct)(fastsimp simp:intra_kind_def)+
  from disj show ?case
  proof
    assume "prog \<turnstile> m -IEdge et\<^isub>2\<rightarrow>\<^isub>p m'"
    with `(Main,m) = n\<^isub>2` `(Main,m') = n\<^isub>2'` 
      `prog \<turnstile> n -IEdge et\<rightarrow>\<^isub>p n'` `(Main,n) = n\<^isub>2` `(Main,n') \<noteq> n\<^isub>2'`
    show ?thesis by(auto dest:WCFG_deterministic)
  next
    assume "\<exists>p es rets. prog \<turnstile> m -CEdge (p, es, rets)\<rightarrow>\<^isub>p m' \<and> et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>"
    with `(Main,m) = n\<^isub>2` `(Main,m') = n\<^isub>2'` 
      `prog \<turnstile> n -IEdge et\<rightarrow>\<^isub>p n'` `(Main,n) = n\<^isub>2` `(Main,n') \<noteq> n\<^isub>2'`
    have False by(fastsimp dest:Proc_CFG_Call_Intra_edge_not_same_source)
    thus ?thesis by simp
  qed
next
  case (Proc p ins outs c n et n')
  from `prog,procs \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(p,n) = n\<^isub>2` `intra_kind et\<^isub>2`
    `(p,ins,outs,c) \<in> set procs` `well_formed procs`
  obtain m m' where "(p,m) = n\<^isub>2" and "(p,m') = n\<^isub>2'"
    and disj:"c \<turnstile> m -IEdge et\<^isub>2\<rightarrow>\<^isub>p m' \<or> 
    (\<exists>p' es' rets'. c \<turnstile> m -CEdge (p',es',rets')\<rightarrow>\<^isub>p m' \<and> et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>)"
    by(induct rule:PCFG.induct)(fastsimp simp:intra_kind_def)+
  from disj show ?case
  proof
    assume "c \<turnstile> m -IEdge et\<^isub>2\<rightarrow>\<^isub>p m'"
    with `(p,m) = n\<^isub>2` `(p,m') = n\<^isub>2'` 
      `c \<turnstile> n -IEdge et\<rightarrow>\<^isub>p n'` `(p,n) = n\<^isub>2` `(p,n') \<noteq> n\<^isub>2'`
    show ?thesis by(auto dest:WCFG_deterministic)
  next
    assume "\<exists>p' es' rets'. c \<turnstile> m -CEdge (p', es', rets')\<rightarrow>\<^isub>p m' \<and> et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>"
    with `(p,m) = n\<^isub>2` `(p,m') = n\<^isub>2'` 
      `c \<turnstile> n -IEdge et\<rightarrow>\<^isub>p n'` `(p,n) = n\<^isub>2` `(p,n') \<noteq> n\<^isub>2'`
    have False by(fastsimp dest:Proc_CFG_Call_Intra_edge_not_same_source)
    thus ?thesis by simp
  qed
next
  case (MainCallReturn n p es rets n' n\<^isub>2 n\<^isub>2')
  from `prog,procs \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(Main,n) = n\<^isub>2`
    `intra_kind et\<^isub>2` `well_formed procs`
  obtain m m' where "(Main,m) = n\<^isub>2" and "(Main,m') = n\<^isub>2'"
    and disj:"prog \<turnstile> m -IEdge et\<^isub>2\<rightarrow>\<^isub>p m' \<or> 
    (\<exists>p es rets. prog \<turnstile> m -CEdge (p,es,rets)\<rightarrow>\<^isub>p m' \<and> et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>)"
    by(induct rule:PCFG.induct)(fastsimp simp:intra_kind_def)+
  from disj show ?case
  proof
    assume "prog \<turnstile> m -IEdge et\<^isub>2\<rightarrow>\<^isub>p m'"
    with `(Main,m) = n\<^isub>2` `(Main,m') = n\<^isub>2'` `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'`
      `(Main, n) = n\<^isub>2` `(Main, n') \<noteq> n\<^isub>2'`
    have False by(fastsimp dest:Proc_CFG_Call_Intra_edge_not_same_source)
    thus ?thesis by simp
  next
    assume "\<exists>p es rets. prog \<turnstile> m -CEdge (p,es,rets)\<rightarrow>\<^isub>p m' \<and> et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>"
    with `(Main,m) = n\<^isub>2` `(Main,m') = n\<^isub>2'` `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'`
      `(Main, n) = n\<^isub>2` `(Main, n') \<noteq> n\<^isub>2'`
    show ?thesis by(fastsimp dest:Proc_CFG_Call_nodes_eq)
  qed
next
  case (ProcCallReturn p ins outs c n p' es rets n' n\<^isub>2 n\<^isub>2')
  from `prog,procs \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(p,n) = n\<^isub>2` `intra_kind et\<^isub>2`
    `(p,ins,outs,c) \<in> set procs` `well_formed procs`
  obtain m m' where "(p,m) = n\<^isub>2" and "(p,m') = n\<^isub>2'"
    and disj:"c \<turnstile> m -IEdge et\<^isub>2\<rightarrow>\<^isub>p m' \<or> 
    (\<exists>p' es' rets'. c \<turnstile> m -CEdge (p',es',rets')\<rightarrow>\<^isub>p m' \<and> et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>)"
    by(induct rule:PCFG.induct)(fastsimp simp:intra_kind_def)+
  from disj show ?case
  proof
    assume "c \<turnstile> m -IEdge et\<^isub>2\<rightarrow>\<^isub>p m'"
    with `(p,m) = n\<^isub>2` `(p,m') = n\<^isub>2'` 
      `c \<turnstile> n -CEdge (p', es, rets)\<rightarrow>\<^isub>p n'` `(p,n) = n\<^isub>2` `(p,n') \<noteq> n\<^isub>2'`
    have False by(fastsimp dest:Proc_CFG_Call_Intra_edge_not_same_source)
    thus ?thesis by simp
  next
    assume "\<exists>p' es' rets'. c \<turnstile> m -CEdge (p', es', rets')\<rightarrow>\<^isub>p m' \<and> et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>"
    with `(p,m) = n\<^isub>2` `(p,m') = n\<^isub>2'` 
      `c \<turnstile> n -CEdge (p', es, rets)\<rightarrow>\<^isub>p n'` `(p,n) = n\<^isub>2` `(p,n') \<noteq> n\<^isub>2'`
    show ?thesis by(fastsimp dest:Proc_CFG_Call_nodes_eq)
  qed
qed(auto simp:intra_kind_def)


subsection {* Well-formedness of programs in combination with a procedure list. *}

definition wf :: "cmd \<Rightarrow> procs \<Rightarrow> bool"
  where "wf prog procs \<equiv> well_formed procs \<and> 
  (\<forall>ps p es rets. containsCall procs prog ps p es rets 
   \<longrightarrow> (distinct rets \<and> 
      (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs \<and> length rets = length outs \<and>
                    length es + 2 = length ins)))"


lemma wf_well_formed [intro]:"wf prog procs \<Longrightarrow> well_formed procs"
  by(simp add:wf_def)


lemma wf_distinct_rets [intro]:
  "\<lbrakk>wf prog procs; containsCall procs prog ps p es rets\<rbrakk> \<Longrightarrow> distinct rets"
by(fastsimp simp:wf_def)


lemma
  assumes "wf prog procs" and "containsCall procs prog ps p es rets"
  and "(p,ins,outs,c) \<in> set procs"
  shows wf_length_retsI:"length rets = length outs"
  and wf_length_esI:"length es + 2 = length ins"
proof -
  from `wf prog procs` have "well_formed procs" by fastsimp
  from `wf prog procs` `containsCall procs prog ps p es rets`
  obtain ins' outs' c' where "(p,ins',outs',c') \<in> set procs"
    and lengths:"length rets = length outs'" "length es + 2 = length ins'"
    by(simp add:wf_def) blast
  from `(p,ins,outs,c) \<in> set procs` `(p,ins',outs',c') \<in> set procs`
    `well_formed procs`
  have "ins' = ins" "outs' = outs" "c' = c" by auto
  with lengths show "length rets = length outs" "length es + 2 = length ins"
    by simp_all
qed


subsection {* Type of well-formed programs *}

typedef wf_prog = "{(prog,procs). wf prog procs}"
by(rule_tac x="(Skip,[])" in exI,simp add:wf_def well_formed_def)

lemma wf_wf_prog:"Rep_wf_prog wfp = (prog,procs) \<Longrightarrow> wf prog procs"
using Rep_wf_prog[of wfp] by(simp add:wf_prog_def)


lemma wfp_Seq1: assumes "Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c\<^isub>1, procs)"
using `Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c\<^isub>1, procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_Seq2: assumes "Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c\<^isub>2, procs)"
using `Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c\<^isub>2, procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_CondTrue: assumes "Rep_wf_prog wfp = (if (b) c\<^isub>1 else c\<^isub>2, procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c\<^isub>1, procs)"
using `Rep_wf_prog wfp = (if (b) c\<^isub>1 else c\<^isub>2, procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c\<^isub>1, procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_CondFalse: assumes "Rep_wf_prog wfp = (if (b) c\<^isub>1 else c\<^isub>2, procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c\<^isub>2, procs)"
using `Rep_wf_prog wfp = (if (b) c\<^isub>1 else c\<^isub>2, procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c\<^isub>2, procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_WhileBody: assumes "Rep_wf_prog wfp = (while (b) c', procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c', procs)"
using `Rep_wf_prog wfp = (while (b) c', procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c', procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_Call: assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "containsCall procs prog ps p es rets"
  obtains wfp' where "Rep_wf_prog wfp' = (c,procs)"
using assms
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c, procs)" in meta_allE)
apply(erule meta_mp) apply(rule Abs_wf_prog_inverse)
by(auto dest:containsCall_indirection simp:wf_prog_def wf_def)



end
