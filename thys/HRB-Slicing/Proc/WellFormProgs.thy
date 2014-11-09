section {* Well-formedness of programs *}

theory WellFormProgs imports PCFG begin

subsection {* Well-formedness of procedure lists. *}

definition wf_proc :: "proc \<Rightarrow> bool"
  where "wf_proc x \<equiv> let (p,ins,outs,c) = x in 
  p \<noteq> Main \<and> distinct ins \<and> distinct outs"

definition well_formed :: "procs \<Rightarrow> bool"
  where "well_formed procs \<equiv> distinct_fst procs \<and> 
  (\<forall>(p,ins,outs,c) \<in> set procs. wf_proc (p,ins,outs,c))"

lemma [dest]:"\<lbrakk>well_formed procs; (Main,ins,outs,c) \<in> set procs\<rbrakk> \<Longrightarrow> False"
  by(fastforce simp:well_formed_def wf_proc_def)

lemma well_formed_same_procs [dest]:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs; (p,ins',outs',c') \<in> set procs\<rbrakk>
  \<Longrightarrow> ins = ins' \<and> outs = outs' \<and> c = c'"
  apply(auto simp:well_formed_def distinct_fst_def distinct_map inj_on_def)
by(erule_tac x="(p,ins,outs,c)" in ballE,auto)+


lemma PCFG_sourcelabel_None_less_num_nodes:
  "\<lbrakk>prog,procs \<turnstile> (Main,Label l) -et\<rightarrow> n'; well_formed procs\<rbrakk> \<Longrightarrow> l < #:prog"
proof(induct "(Main,Label l)" et n' 
      arbitrary:l rule:PCFG.induct)
  case (Main et n')
  from `prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'`
  show ?case by(fastforce elim:Proc_CFG_sourcelabel_less_num_nodes)
next
  case (MainCall l p es rets n' ins outs c)
  from `prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'`
  show ?case by(fastforce elim:Proc_CFG_sourcelabel_less_num_nodes)
next
  case (MainCallReturn p es rets n' l)
  from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
  show ?case by(fastforce elim:Proc_CFG_sourcelabel_less_num_nodes)
qed auto

lemma Proc_CFG_sourcelabel_Some_less_num_nodes:
  "\<lbrakk>prog,procs \<turnstile> (p,Label l) -et\<rightarrow> n'; (p,ins,outs,c) \<in> set procs; 
    well_formed procs\<rbrakk> \<Longrightarrow> l < #:c"
proof(induct "(p,Label l)" et n' arbitrary:l rule:PCFG.induct)
  case (Proc ins' outs' c' et n')
  from `c' \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'` have "l < #:c'"
    by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
  with `well_formed procs` `(p,ins,outs,c) \<in> set procs` 
    `(p,ins',outs',c') \<in> set procs`
  show ?case by fastforce
next
  case (ProcCall ins' outs' c' l' p' es rets l'' ins'' outs'' c'' ps)
  from `c' \<turnstile> Label l' -CEdge (p',es,rets)\<rightarrow>\<^sub>p Label l''` have "l' < #:c'"
    by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
  with `well_formed procs` `(p,ins,outs,c) \<in> set procs` 
    `(p, ins', outs', c') \<in> set procs`
  show ?case by fastforce
next
  case (ProcCallReturn ins' outs' c' p' es rets n')
  from `c' \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'` have "l < #:c'"
    by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
  with `well_formed procs` `(p,ins,outs,c) \<in> set procs` 
    `(p,ins',outs',c') \<in> set procs`
  show ?case by fastforce
qed auto


lemma Proc_CFG_targetlabel_Main_less_num_nodes:
  "\<lbrakk>prog,procs \<turnstile> n -et\<rightarrow> (Main,Label l); well_formed procs\<rbrakk> \<Longrightarrow> l < #:prog"
proof(induct n et "(Main,Label l)" 
      arbitrary:l rule:PCFG.induct)
  case (Main n et)
  from `prog \<turnstile> n -IEdge et\<rightarrow>\<^sub>p Label l`
  show ?case by(fastforce elim:Proc_CFG_targetlabel_less_num_nodes)
next
  case (MainReturn l' p es rets l'' ins outs c)
  from `prog \<turnstile> Label l' -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l''` 
  show ?case by(fastforce elim:Proc_CFG_targetlabel_less_num_nodes)
next
  case (MainCallReturn n p es rets)
  from `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l`
  show ?case by(fastforce elim:Proc_CFG_targetlabel_less_num_nodes)
qed auto


lemma Proc_CFG_targetlabel_Some_less_num_nodes:
  "\<lbrakk>prog,procs \<turnstile> n -et\<rightarrow> (p,Label l); (p,ins,outs,c) \<in> set procs; 
    well_formed procs\<rbrakk> \<Longrightarrow> l < #:c"
proof(induct n et "(p,Label l)" arbitrary:l rule:PCFG.induct)
  case (Proc ins' outs' c' n et)
  from `c' \<turnstile> n -IEdge et\<rightarrow>\<^sub>p Label l` have "l < #:c'"
    by(fastforce intro:Proc_CFG_targetlabel_less_num_nodes)
  with `well_formed procs` `(p,ins,outs,c) \<in> set procs` 
    `(p,ins',outs',c') \<in> set procs`
  show ?case by fastforce
next
  case (ProcReturn ins' outs' c' l' p' es rets l ins'' outs'' c'' ps)
  from `c' \<turnstile> Label l' -CEdge (p',es,rets)\<rightarrow>\<^sub>p Label l` have "l < #:c'"
    by(fastforce intro:Proc_CFG_targetlabel_less_num_nodes)
  with `well_formed procs` `(p,ins,outs,c) \<in> set procs` 
    `(p, ins', outs', c') \<in> set procs`
  show ?case by fastforce
next
  case (ProcCallReturn ins' outs' c' n p'' es rets)
  from `c' \<turnstile> n -CEdge (p'', es, rets)\<rightarrow>\<^sub>p Label l` have "l < #:c'"
    by(fastforce intro:Proc_CFG_targetlabel_less_num_nodes)
  with `well_formed procs` `(p,ins,outs,c) \<in> set procs` 
    `(p,ins',outs',c') \<in> set procs`
  show ?case by fastforce
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
    where "prog \<turnstile> Label l -CEdge (p,es',rets')\<rightarrow>\<^sub>p n''" 
    and "(p,ins',outs',c') \<in> set procs" 
    and "et' = (\<lambda>s. True):(Main,n'')\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es'"
    by(auto elim:PCFG.cases)
  from `(p,ins,outs,c) \<in> set procs` `(p,ins',outs',c') \<in> set procs`
    `well_formed procs`
  have "ins = ins'" by fastforce
  from `prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'`
    `prog \<turnstile> Label l -CEdge (p,es',rets')\<rightarrow>\<^sub>p n''`
  have "es = es'" and "n' = n''" by(auto dest:Proc_CFG_Call_nodes_eq)
  with `et' = (\<lambda>s. True):(Main,n'')\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es'` `ins = ins'`
  show ?case by simp
next
  case (ProcCall p ins outs c l p' es' rets' l' ins' outs' c' ps)
  from `prog,procs \<turnstile> (p,Label l) -et'\<rightarrow> (p',Entry)` `(p',ins',outs',c') \<in> set procs` 
    `(p, ins, outs, c) \<in> set procs` `well_formed procs`
    `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
  show ?case
  proof(induct "(p,Label l)" et' "(p',Entry)" rule:PCFG.induct)
    case (ProcCall insx outsx cx es'x rets'x l'x ins'x outs'x c'x ps)
    from `well_formed procs` `(p, insx, outsx, cx) \<in> set procs` 
      `(p, ins, outs, c) \<in> set procs`
    have [simp]:"cx = c" by auto
    from `cx \<turnstile> Label l -CEdge (p', es'x, rets'x)\<rightarrow>\<^sub>p Label l'x`
      `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
    have [simp]:"es'x = es'" "l'x = l'" by(auto dest:Proc_CFG_Call_nodes_eq)
    show ?case by simp
  qed auto
next
  case MainReturn
  thus ?case by -(erule PCFG.cases,auto dest:Proc_CFG_Call_nodes_eq')
next
  case (ProcReturn p ins outs c l p' es' rets' l' ins' outs' c' ps)
  from `prog,procs \<turnstile> (p',Exit) -et'\<rightarrow> (p, Label l')`
    `(p, ins, outs, c) \<in> set procs` `(p', ins', outs', c') \<in> set procs`
    `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'` 
    `containsCall procs prog ps p` `well_formed procs`
  show ?case
  proof(induct "(p',Exit)" et' "(p,Label l')" rule:PCFG.induct)
    case (ProcReturn insx outsx cx lx es'x rets'x ins'x outs'x c'x psx)
    from `(p', ins'x, outs'x, c'x) \<in> set procs`
      `(p', ins', outs', c') \<in> set procs` `well_formed procs`
    have [simp]:"outs'x = outs'" by fastforce
    from `(p, insx, outsx, cx) \<in> set procs` `(p, ins, outs, c) \<in> set procs`
      `well_formed procs`
    have [simp]:"cx = c" by auto
    from `cx \<turnstile> Label lx -CEdge (p', es'x, rets'x)\<rightarrow>\<^sub>p Label l'`
      `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
    have [simp]:"rets'x = rets'" by(fastforce dest:Proc_CFG_Call_nodes_eq')
    show ?case by simp
  qed auto
next
  case MainCallReturn thus ?case by(auto elim:PCFG.cases dest:Proc_CFG_edge_det)
next
  case ProcCallReturn thus ?case by(auto elim:PCFG.cases dest:Proc_CFG_edge_det)
qed


lemma Proc_CFG_deterministic:
  "\<lbrakk>prog,procs \<turnstile> n\<^sub>1 -et\<^sub>1\<rightarrow> n\<^sub>1'; prog,procs \<turnstile> n\<^sub>2 -et\<^sub>2\<rightarrow> n\<^sub>2'; n\<^sub>1 = n\<^sub>2; n\<^sub>1' \<noteq> n\<^sub>2'; 
   intra_kind et\<^sub>1; intra_kind et\<^sub>2; well_formed procs\<rbrakk>
  \<Longrightarrow> \<exists>Q Q'. et\<^sub>1 = (Q)\<^sub>\<surd> \<and> et\<^sub>2 = (Q')\<^sub>\<surd> \<and> 
            (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
proof(induct arbitrary:n\<^sub>2 n\<^sub>2' rule:PCFG.induct)
  case (Main n et n')
  from `prog,procs \<turnstile> n\<^sub>2 -et\<^sub>2\<rightarrow> n\<^sub>2'` `(Main,n) = n\<^sub>2`
    `intra_kind et\<^sub>2` `well_formed procs`
  obtain m m' where "(Main,m) = n\<^sub>2" and "(Main,m') = n\<^sub>2'"
    and disj:"prog \<turnstile> m -IEdge et\<^sub>2\<rightarrow>\<^sub>p m' \<or> 
    (\<exists>p es rets. prog \<turnstile> m -CEdge (p,es,rets)\<rightarrow>\<^sub>p m' \<and> et\<^sub>2 = (\<lambda>s. False)\<^sub>\<surd>)"
    by(induct rule:PCFG.induct)(fastforce simp:intra_kind_def)+
  from disj show ?case
  proof
    assume "prog \<turnstile> m -IEdge et\<^sub>2\<rightarrow>\<^sub>p m'"
    with `(Main,m) = n\<^sub>2` `(Main,m') = n\<^sub>2'` 
      `prog \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'` `(Main,n) = n\<^sub>2` `(Main,n') \<noteq> n\<^sub>2'`
    show ?thesis by(auto dest:WCFG_deterministic)
  next
    assume "\<exists>p es rets. prog \<turnstile> m -CEdge (p, es, rets)\<rightarrow>\<^sub>p m' \<and> et\<^sub>2 = (\<lambda>s. False)\<^sub>\<surd>"
    with `(Main,m) = n\<^sub>2` `(Main,m') = n\<^sub>2'` 
      `prog \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'` `(Main,n) = n\<^sub>2` `(Main,n') \<noteq> n\<^sub>2'`
    have False by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_source)
    thus ?thesis by simp
  qed
next
  case (Proc p ins outs c n et n')
  from `prog,procs \<turnstile> n\<^sub>2 -et\<^sub>2\<rightarrow> n\<^sub>2'` `(p,n) = n\<^sub>2` `intra_kind et\<^sub>2`
    `(p,ins,outs,c) \<in> set procs` `well_formed procs`
  obtain m m' where "(p,m) = n\<^sub>2" and "(p,m') = n\<^sub>2'"
    and disj:"c \<turnstile> m -IEdge et\<^sub>2\<rightarrow>\<^sub>p m' \<or> 
    (\<exists>p' es' rets'. c \<turnstile> m -CEdge (p',es',rets')\<rightarrow>\<^sub>p m' \<and> et\<^sub>2 = (\<lambda>s. False)\<^sub>\<surd>)"
    by(induct rule:PCFG.induct)(fastforce simp:intra_kind_def)+
  from disj show ?case
  proof
    assume "c \<turnstile> m -IEdge et\<^sub>2\<rightarrow>\<^sub>p m'"
    with `(p,m) = n\<^sub>2` `(p,m') = n\<^sub>2'` 
      `c \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'` `(p,n) = n\<^sub>2` `(p,n') \<noteq> n\<^sub>2'`
    show ?thesis by(auto dest:WCFG_deterministic)
  next
    assume "\<exists>p' es' rets'. c \<turnstile> m -CEdge (p', es', rets')\<rightarrow>\<^sub>p m' \<and> et\<^sub>2 = (\<lambda>s. False)\<^sub>\<surd>"
    with `(p,m) = n\<^sub>2` `(p,m') = n\<^sub>2'` 
      `c \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'` `(p,n) = n\<^sub>2` `(p,n') \<noteq> n\<^sub>2'`
    have False by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_source)
    thus ?thesis by simp
  qed
next
  case (MainCallReturn n p es rets n' n\<^sub>2 n\<^sub>2')
  from `prog,procs \<turnstile> n\<^sub>2 -et\<^sub>2\<rightarrow> n\<^sub>2'` `(Main,n) = n\<^sub>2`
    `intra_kind et\<^sub>2` `well_formed procs`
  obtain m m' where "(Main,m) = n\<^sub>2" and "(Main,m') = n\<^sub>2'"
    and disj:"prog \<turnstile> m -IEdge et\<^sub>2\<rightarrow>\<^sub>p m' \<or> 
    (\<exists>p es rets. prog \<turnstile> m -CEdge (p,es,rets)\<rightarrow>\<^sub>p m' \<and> et\<^sub>2 = (\<lambda>s. False)\<^sub>\<surd>)"
    by(induct rule:PCFG.induct)(fastforce simp:intra_kind_def)+
  from disj show ?case
  proof
    assume "prog \<turnstile> m -IEdge et\<^sub>2\<rightarrow>\<^sub>p m'"
    with `(Main,m) = n\<^sub>2` `(Main,m') = n\<^sub>2'` `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
      `(Main, n) = n\<^sub>2` `(Main, n') \<noteq> n\<^sub>2'`
    have False by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_source)
    thus ?thesis by simp
  next
    assume "\<exists>p es rets. prog \<turnstile> m -CEdge (p,es,rets)\<rightarrow>\<^sub>p m' \<and> et\<^sub>2 = (\<lambda>s. False)\<^sub>\<surd>"
    with `(Main,m) = n\<^sub>2` `(Main,m') = n\<^sub>2'` `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
      `(Main, n) = n\<^sub>2` `(Main, n') \<noteq> n\<^sub>2'`
    show ?thesis by(fastforce dest:Proc_CFG_Call_nodes_eq)
  qed
next
  case (ProcCallReturn p ins outs c n p' es rets n' ps n\<^sub>2 n\<^sub>2')
  from `prog,procs \<turnstile> n\<^sub>2 -et\<^sub>2\<rightarrow> n\<^sub>2'` `(p,n) = n\<^sub>2` `intra_kind et\<^sub>2`
    `(p,ins,outs,c) \<in> set procs` `well_formed procs`
  obtain m m' where "(p,m) = n\<^sub>2" and "(p,m') = n\<^sub>2'"
    and disj:"c \<turnstile> m -IEdge et\<^sub>2\<rightarrow>\<^sub>p m' \<or> 
    (\<exists>p' es' rets'. c \<turnstile> m -CEdge (p',es',rets')\<rightarrow>\<^sub>p m' \<and> et\<^sub>2 = (\<lambda>s. False)\<^sub>\<surd>)"
    by(induct rule:PCFG.induct)(fastforce simp:intra_kind_def)+
  from disj show ?case
  proof
    assume "c \<turnstile> m -IEdge et\<^sub>2\<rightarrow>\<^sub>p m'"
    with `(p,m) = n\<^sub>2` `(p,m') = n\<^sub>2'` 
      `c \<turnstile> n -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'` `(p,n) = n\<^sub>2` `(p,n') \<noteq> n\<^sub>2'`
    have False by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_source)
    thus ?thesis by simp
  next
    assume "\<exists>p' es' rets'. c \<turnstile> m -CEdge (p', es', rets')\<rightarrow>\<^sub>p m' \<and> et\<^sub>2 = (\<lambda>s. False)\<^sub>\<surd>"
    with `(p,m) = n\<^sub>2` `(p,m') = n\<^sub>2'` 
      `c \<turnstile> n -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'` `(p,n) = n\<^sub>2` `(p,n') \<noteq> n\<^sub>2'`
    show ?thesis by(fastforce dest:Proc_CFG_Call_nodes_eq)
  qed
qed(auto simp:intra_kind_def)


subsection {* Well-formedness of programs in combination with a procedure list. *}

definition wf :: "cmd \<Rightarrow> procs \<Rightarrow> bool"
  where "wf prog procs \<equiv> well_formed procs \<and> 
  (\<forall>ps p. containsCall procs prog ps p \<longrightarrow> (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs \<and> 
          (\<forall>c' n n' es rets. c' \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p n' \<longrightarrow>
               distinct rets \<and> length rets = length outs \<and> length es = length ins)))"


lemma wf_well_formed [intro]:"wf prog procs \<Longrightarrow> well_formed procs"
  by(simp add:wf_def)


lemma wf_distinct_rets [intro]:
  "\<lbrakk>wf prog procs; containsCall procs prog ps p; (p,ins,outs,c) \<in> set procs;
    c' \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'\<rbrakk> \<Longrightarrow> distinct rets"
by(fastforce simp:wf_def)


lemma
  assumes "wf prog procs" and "containsCall procs prog ps p"
  and "(p,ins,outs,c) \<in> set procs" and "c' \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'"
  shows wf_length_retsI [intro]:"length rets = length outs"
  and wf_length_esI [intro]:"length es = length ins"
proof -
  from `wf prog procs` have "well_formed procs" by fastforce
  from assms
  obtain ins' outs' c' where "(p,ins',outs',c') \<in> set procs"
    and lengths:"length rets = length outs'" "length es = length ins'"
    by(simp add:wf_def) blast
  from `(p,ins,outs,c) \<in> set procs` `(p,ins',outs',c') \<in> set procs`
    `well_formed procs`
  have "ins' = ins" "outs' = outs" "c' = c" by auto
  with lengths show "length rets = length outs" "length es = length ins"
    by simp_all
qed


subsection {* Type of well-formed programs *}

definition "wf_prog = {(prog,procs). wf prog procs}"

typedef wf_prog = wf_prog
  unfolding wf_prog_def
  apply (rule_tac x="(Skip,[])" in exI)
  apply (simp add:wf_def well_formed_def)
  done

lemma wf_wf_prog:"Rep_wf_prog wfp = (prog,procs) \<Longrightarrow> wf prog procs"
using Rep_wf_prog[of wfp] by(simp add:wf_prog_def)


lemma wfp_Seq1: assumes "Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c\<^sub>1, procs)"
using `Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c\<^sub>1, procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_Seq2: assumes "Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c\<^sub>2, procs)"
using `Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c\<^sub>2, procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_CondTrue: assumes "Rep_wf_prog wfp = (if (b) c\<^sub>1 else c\<^sub>2, procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c\<^sub>1, procs)"
using `Rep_wf_prog wfp = (if (b) c\<^sub>1 else c\<^sub>2, procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c\<^sub>1, procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_CondFalse: assumes "Rep_wf_prog wfp = (if (b) c\<^sub>1 else c\<^sub>2, procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c\<^sub>2, procs)"
using `Rep_wf_prog wfp = (if (b) c\<^sub>1 else c\<^sub>2, procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c\<^sub>2, procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_WhileBody: assumes "Rep_wf_prog wfp = (while (b) c', procs)"
  obtains wfp' where "Rep_wf_prog wfp' = (c', procs)"
using `Rep_wf_prog wfp = (while (b) c', procs)`
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c', procs)" in meta_allE)
by(auto elim:meta_mp simp:Abs_wf_prog_inverse wf_prog_def wf_def)

lemma wfp_Call: assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "containsCall procs prog ps p"
  obtains wfp' where "Rep_wf_prog wfp' = (c,procs)"
using assms
apply(cases wfp) apply(auto simp:Abs_wf_prog_inverse wf_prog_def wf_def)
apply(erule_tac x="Abs_wf_prog (c, procs)" in meta_allE)
apply(erule meta_mp) apply(rule Abs_wf_prog_inverse)
by(auto dest:containsCall_indirection simp:wf_prog_def wf_def)



end
