header {* \isaheader{Lemmas concerning paths to instantiate locale
  Postdomination} *}

theory ValidPaths imports WellFormed "../StaticInter/Postdomination" begin

subsection {* Intraprocedural paths from method entry and to method exit *}


abbreviation path :: "wf_prog \<Rightarrow> node \<Rightarrow> edge list \<Rightarrow> node \<Rightarrow> bool" ("_ \<turnstile> _ -_\<rightarrow>* _")
  where "wfp \<turnstile> n -as\<rightarrow>* n' \<equiv> CFG.path sourcenode targetnode (valid_edge wfp) n as n'"

definition label_incrs :: "edge list \<Rightarrow> nat \<Rightarrow> edge list" ("_ \<oplus>s _" 60)
  where "as \<oplus>s i \<equiv> map (\<lambda>((p,n),et,(p',n')). ((p,n \<oplus> i),et,(p',n' \<oplus> i))) as"


declare One_nat_def [simp del]



subsubsection {* From @{text prog} to @{text "prog;;c\<^isub>2"} *}

lemma Proc_CFG_edge_SeqFirst_source_Label:
  assumes "prog \<turnstile> Label l -et\<rightarrow>\<^isub>p n'"
  obtains nx where "prog;;c\<^isub>2 \<turnstile> Label l -et\<rightarrow>\<^isub>p nx"
proof(atomize_elim)
  from `prog \<turnstile> Label l -et\<rightarrow>\<^isub>p n'` obtain n where "prog \<turnstile> n -et\<rightarrow>\<^isub>p n'" and "Label l = n"
    by simp
  thus "\<exists>nx. prog;;c\<^isub>2 \<turnstile> Label l -et\<rightarrow>\<^isub>p nx"
  proof(induct prog n et n' rule:Proc_CFG.induct)
    case (Proc_CFG_SeqSecond c\<^isub>2' n et n' c\<^isub>1)
    show ?case
    proof(cases "n' = Exit")
      case True
      with `c\<^isub>2' \<turnstile> n -et\<rightarrow>\<^isub>p n'` `n \<noteq> Entry` have "c\<^isub>1;; c\<^isub>2' \<turnstile> n \<oplus> #:c\<^isub>1 -et\<rightarrow>\<^isub>p Exit \<oplus> #:c\<^isub>1"
	by(fastsimp intro:Proc_CFG.Proc_CFG_SeqSecond)
      moreover from `n \<noteq> Entry` have "n \<oplus> #:c\<^isub>1 \<noteq> Entry" by(cases n) auto
      ultimately
      have "c\<^isub>1;; c\<^isub>2';; c\<^isub>2 \<turnstile> n \<oplus> #:c\<^isub>1 -et\<rightarrow>\<^isub>p Label (#:c\<^isub>1;; c\<^isub>2')"
	by(fastsimp intro:Proc_CFG_SeqConnect)
      with `Label l = n \<oplus> #:c\<^isub>1` show ?thesis by fastsimp
    next
      case False
      with Proc_CFG_SeqSecond
      have "(c\<^isub>1;; c\<^isub>2');; c\<^isub>2 \<turnstile> n \<oplus> #:c\<^isub>1 -et\<rightarrow>\<^isub>p n' \<oplus> #:c\<^isub>1"
	by(fastsimp intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_SeqSecond)
      with `Label l = n \<oplus> #:c\<^isub>1` show ?thesis by fastsimp
    qed
  next
    case (Proc_CFG_CondThen c\<^isub>1 n et n' b c\<^isub>2')
    show ?case
    proof(cases "n' = Exit")
      case True
      with `c\<^isub>1 \<turnstile> n -et\<rightarrow>\<^isub>p n'` `n \<noteq> Entry`
      have "if (b) c\<^isub>1 else c\<^isub>2' \<turnstile> n \<oplus> 1 -et\<rightarrow>\<^isub>p Exit \<oplus> 1"
	by(fastsimp intro:Proc_CFG.Proc_CFG_CondThen)
      moreover from `n \<noteq> Entry` have "n \<oplus> 1 \<noteq> Entry" by(cases n) auto
      ultimately
      have "if (b) c\<^isub>1 else c\<^isub>2';; c\<^isub>2 \<turnstile> n \<oplus> 1 -et\<rightarrow>\<^isub>p Label (#:if (b) c\<^isub>1 else c\<^isub>2')"
	by(fastsimp intro:Proc_CFG_SeqConnect)
      with `Label l = n \<oplus> 1` show ?thesis by fastsimp
    next
      case False
      hence "n' \<oplus> 1 \<noteq> Exit" by(cases n') auto
      with Proc_CFG_CondThen
      have  "if (b) c\<^isub>1 else c\<^isub>2';; c\<^isub>2 \<turnstile> Label l -et\<rightarrow>\<^isub>p n' \<oplus> 1"
	by(fastsimp intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_CondThen)
      with `Label l = n \<oplus> 1` show ?thesis by fastsimp
    qed
  next
    case (Proc_CFG_CondElse c\<^isub>1 n et n' b c\<^isub>2')
    show ?case
    proof(cases "n' = Exit")
      case True
      with `c\<^isub>1 \<turnstile> n -et\<rightarrow>\<^isub>p n'` `n \<noteq> Entry`
      have "if (b) c\<^isub>2' else c\<^isub>1 \<turnstile> n \<oplus> (#:c\<^isub>2' + 1) -et\<rightarrow>\<^isub>p Exit \<oplus> (#:c\<^isub>2' + 1)"
	by(fastsimp intro:Proc_CFG.Proc_CFG_CondElse)
      moreover from `n \<noteq> Entry` have "n \<oplus> (#:c\<^isub>2' + 1) \<noteq> Entry" by(cases n) auto
      ultimately
      have "if (b) c\<^isub>2' else c\<^isub>1;; c\<^isub>2 \<turnstile> n \<oplus> (#:c\<^isub>2' + 1) -et\<rightarrow>\<^isub>p 
	Label (#:if (b) c\<^isub>2' else c\<^isub>1)"
	by(fastsimp intro:Proc_CFG_SeqConnect)
      with `Label l = n \<oplus> (#:c\<^isub>2' + 1)` show ?thesis by fastsimp
    next
      case False
      hence "n' \<oplus> (#:c\<^isub>2' + 1) \<noteq> Exit" by(cases n') auto
      with Proc_CFG_CondElse
      have  "if (b) c\<^isub>2' else c\<^isub>1 ;; c\<^isub>2 \<turnstile> Label l -et\<rightarrow>\<^isub>p n' \<oplus> (#:c\<^isub>2' + 1)"
	by(fastsimp intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_CondElse)
      with `Label l = n \<oplus> (#:c\<^isub>2' + 1)` show ?thesis by fastsimp
    qed
  qed (auto intro:Proc_CFG.intros)
qed

lemma Proc_CFG_edge_SeqFirst_target_Label:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^isub>p n'; Label l' = n'\<rbrakk> \<Longrightarrow> prog;;c\<^isub>2 \<turnstile> n -et\<rightarrow>\<^isub>p Label l'"
proof(induct prog n et n' rule:Proc_CFG.induct)
  case (Proc_CFG_SeqSecond c\<^isub>2' n et n' c\<^isub>1)
  from `Label l' = n' \<oplus> #:c\<^isub>1` have "n' \<noteq> Exit" by(cases n') auto
  with Proc_CFG_SeqSecond
  show ?case by(fastsimp intro:Proc_CFG_SeqFirst intro:Proc_CFG.Proc_CFG_SeqSecond)
next
  case (Proc_CFG_CondThen c\<^isub>1 n et n' b c\<^isub>2')
  from `Label l' = n' \<oplus> 1` have "n' \<noteq> Exit" by(cases n') auto
  with Proc_CFG_CondThen
  show ?case by(fastsimp intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_CondThen)
qed (auto intro:Proc_CFG.intros)


lemma PCFG_edge_SeqFirst_source_Label:
  assumes "prog,procs \<turnstile> (p,Label l) -et\<rightarrow> (p',n')"
  obtains nx where "prog;;c\<^isub>2,procs \<turnstile> (p,Label l) -et\<rightarrow> (p',nx)"
proof(atomize_elim)
  from `prog,procs \<turnstile> (p,Label l) -et\<rightarrow> (p',n')`
  show "\<exists>nx. prog;;c\<^isub>2,procs \<turnstile> (p,Label l) -et\<rightarrow> (p',nx)"
  proof(induct x\<equiv>"(p,Label l)" et x'\<equiv>"(p',n')" rule:PCFG.induct)
    case (Main n et nx)
    from `prog \<turnstile> n -IEdge et\<rightarrow>\<^isub>p nx` `(Main, n) = (p, Label l)`
    obtain nx' where "prog;;c\<^isub>2 \<turnstile> n -IEdge et\<rightarrow>\<^isub>p nx'"
      by(auto elim:Proc_CFG_edge_SeqFirst_source_Label)
    with `(Main, n) = (p, Label l)` `(Main, nx) = (p', n')` show ?case 
      by(fastsimp dest:PCFG.Main)
  next
    case (Proc px ins outs c n et nx ps es rets)
    from `containsCall procs prog ps px es rets` 
    have "containsCall procs (prog;;c\<^isub>2) ps px es rets" by simp
    with Proc show ?case by(fastsimp dest:PCFG.Proc)
  next
    case (MainCall lx px es rets nx ins outs c)
    from `prog \<turnstile> Label lx -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx`
    obtain nx' where "prog;;c\<^isub>2 \<turnstile> Label lx -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx'"
      by(auto elim:Proc_CFG_edge_SeqFirst_source_Label)
    with MainCall show ?case by(fastsimp dest:PCFG.MainCall)
  next
    case (ProcCall i px ins outs c lx px' es' rets' l' ins' outs' c' ps es rets)
    from `containsCall procs prog ps px es rets` 
    have "containsCall procs (prog;;c\<^isub>2) ps px es rets" by simp
    with ProcCall show ?case by(fastsimp dest!:PCFG.ProcCall)
  next
    case (MainReturn lx px es rets l' ins outs c)
    from `prog \<turnstile> Label lx -CEdge (px, es, rets)\<rightarrow>\<^isub>p Label l'`
    obtain nx' where "prog;;c\<^isub>2 \<turnstile> Label lx -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx'"
      by(auto elim:Proc_CFG_edge_SeqFirst_source_Label)
    with MainReturn show ?case by(fastsimp dest:PCFG.MainReturn)
  next
    case (ProcReturn i px ins outs c lx px' es' rets' l' ins' outs' c' ps es rets)
    from `containsCall procs prog ps px es rets` 
    have "containsCall procs (prog;;c\<^isub>2) ps px es rets" by simp
    with ProcReturn show ?case by(fastsimp dest!:PCFG.ProcReturn)
  next
    case (MainCallReturn n px es rets nx')
    from `prog \<turnstile> n -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx'` `(Main, n) = (p, Label l)`
    obtain nx'' where "prog;;c\<^isub>2 \<turnstile> n -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx''"
      by(auto elim:Proc_CFG_edge_SeqFirst_source_Label)
    with MainCallReturn show ?case by(fastsimp dest:PCFG.MainCallReturn)
  next
    case (ProcCallReturn px ins outs c n px' es' rets' nx' ps es rets)
    from `containsCall procs prog ps px es rets`
    have "containsCall procs (prog;;c\<^isub>2) ps px es rets" by simp
    with ProcCallReturn show ?case by(fastsimp dest!:PCFG.ProcCallReturn)
  qed
qed


lemma PCFG_edge_SeqFirst_target_Label:
  "prog,procs \<turnstile> (p,n) -et\<rightarrow> (p',Label l') 
  \<Longrightarrow> prog;;c\<^isub>2,procs \<turnstile> (p,n) -et\<rightarrow> (p',Label l')"
proof(induct x\<equiv>"(p,n)" et x'\<equiv>"(p',Label l')" rule:PCFG.induct)
  case Main
  thus ?case by(fastsimp dest:Proc_CFG_edge_SeqFirst_target_Label intro:PCFG.Main)
next
  case (Proc px ins outs c n et nx ps es rets)
  from `containsCall procs prog ps px es rets` 
  have "containsCall procs (prog;;c\<^isub>2) ps px es rets" by simp
  with Proc show ?case by(fastsimp dest:PCFG.Proc)
next
  case MainCall
  thus ?case by(fastsimp dest:Proc_CFG_edge_SeqFirst_target_Label intro:PCFG.MainCall)
next
  case (ProcCall i px ins outs c lx px' es' rets' l' ins' outs' c' ps es rets)
  from `containsCall procs prog ps px es rets` 
  have "containsCall procs (prog;;c\<^isub>2) ps px es rets" by simp
  with ProcCall show ?case by(fastsimp dest!:PCFG.ProcCall)
next
  case MainReturn thus ?case
    by(fastsimp dest:Proc_CFG_edge_SeqFirst_target_Label 
               intro!:PCFG.MainReturn[simplified])
next
  case (ProcReturn i px ins outs c lx px' es' rets' l' ins' outs' c' ps es rets)
  from `containsCall procs prog ps px es rets` 
  have "containsCall procs (prog;;c\<^isub>2) ps px es rets" by simp
  with ProcReturn show ?case by(fastsimp dest!:PCFG.ProcReturn)
next
  case MainCallReturn thus ?case
  by(fastsimp dest:Proc_CFG_edge_SeqFirst_target_Label intro:PCFG.MainCallReturn)
next
  case (ProcCallReturn px ins outs c n px' es' rets' nx' ps es rets)
  from `containsCall procs prog ps px es rets` 
  have "containsCall procs (prog;;c\<^isub>2) ps px es rets" by simp
  with ProcCallReturn show ?case by(fastsimp dest!:PCFG.ProcCallReturn)
qed


lemma path_SeqFirst:
  assumes "Rep_wf_prog wfp = (prog,procs)" and "Rep_wf_prog wfp' = (prog;;c\<^isub>2,procs)"
  shows "\<lbrakk>wfp \<turnstile> (p,n) -as\<rightarrow>* (p,Label l); \<forall>a \<in> set as. intra_kind (kind a)\<rbrakk>
  \<Longrightarrow> wfp' \<turnstile> (p,n) -as\<rightarrow>* (p,Label l)"
proof(induct x\<equiv>"(p,n)" as x'\<equiv>"(p,Label l)" arbitrary:n rule:ProcCFG.path.induct)
  case (empty_path m)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) m` 
    `m = (p,Label l)` `Rep_wf_prog wfp = (prog, procs)` 
    `Rep_wf_prog wfp' = (prog;; c\<^isub>2, procs)`
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') m"
    apply(auto simp:ProcCFG.valid_node_def valid_edge_def)
    apply(erule PCFG_edge_SeqFirst_source_Label,fastsimp)
    by(drule PCFG_edge_SeqFirst_target_Label,fastsimp)
  with `m = (p,Label l)` `m = (p, n)` show ?case
    by(fastsimp intro:ProcCFG.empty_path)
next
  case (Cons_path n'' as n' a nx)
  note IH = `\<And>n. \<lbrakk>\<forall>a\<in>set as. intra_kind (kind a); n'' = (p, n); 
    n' = (p, Label l)\<rbrakk> \<Longrightarrow> wfp' \<turnstile> (p, n) -as\<rightarrow>* (p, Label l)`
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` `Rep_wf_prog wfp' = (prog;;c\<^isub>2,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `\<forall>a\<in>set (a # as). intra_kind (kind a)` have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from `valid_edge wfp a` `sourcenode a = nx` `targetnode a = n''`
    `intra_kind (kind a)` `nx = (p, n)` wf 
  obtain nx' where "n'' = (p,nx')"
    by(auto elim:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF `\<forall>a\<in>set as. intra_kind (kind a)` this `n' = (p, Label l)`]
  have path:"wfp' \<turnstile> (p, nx') -as\<rightarrow>* (p, Label l)" .
  have "valid_edge wfp' a"
  proof(cases nx')
    case (Label lx)
    with `valid_edge wfp a` `sourcenode a = nx` `targetnode a = n''`
      `nx = (p, n)` `n'' = (p,nx')` show ?thesis
      by(fastsimp intro:PCFG_edge_SeqFirst_target_Label 
	           simp:intra_kind_def valid_edge_def)
  next
    case Entry
    with `valid_edge wfp a` `targetnode a = n''` `n'' = (p,nx')`
      `intra_kind (kind a)` have False 
      by(auto elim:PCFG.cases simp:valid_edge_def intra_kind_def)
    thus ?thesis by simp
  next
    case Exit
    with path `\<forall>a\<in>set as. intra_kind (kind a)` have False 
      by(induct x\<equiv>"(p,nx')" as x'\<equiv>"(p,Label l)" rule:ProcCFG.path.induct)
    (auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
    thus ?thesis by simp
  qed
  with `sourcenode a = nx` `targetnode a = n''` `nx = (p, n)` `n'' = (p,nx')` path
  show ?case by(fastsimp intro:ProcCFG.Cons_path)
qed


subsubsection {* From @{text prog} to @{text "c\<^isub>1;;prog"} *}

lemma Proc_CFG_edge_SeqSecond_source_not_Entry:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^isub>p n'; n \<noteq> Entry\<rbrakk> \<Longrightarrow> c\<^isub>1;;prog \<turnstile> n \<oplus> #:c\<^isub>1 -et\<rightarrow>\<^isub>p n' \<oplus> #:c\<^isub>1"
by(induct rule:Proc_CFG.induct)(fastsimp intro:Proc_CFG_SeqSecond Proc_CFG.intros)+


lemma PCFG_Main_edge_SeqSecond_source_not_Entry:
  "\<lbrakk>prog,procs \<turnstile> (Main,n) -et\<rightarrow> (p',n'); n \<noteq> Entry; intra_kind et; well_formed procs\<rbrakk>
  \<Longrightarrow> c\<^isub>1;;prog,procs \<turnstile> (Main,n \<oplus> #:c\<^isub>1) -et\<rightarrow> (p',n' \<oplus> #:c\<^isub>1)"
proof(induct x\<equiv>"(Main,n)" et x'\<equiv>"(p',n')" rule:PCFG.induct)
  case Main
  thus ?case
    by(fastsimp dest:Proc_CFG_edge_SeqSecond_source_not_Entry intro:PCFG.Main)
next
  case (MainCallReturn nx p es rets nx')
  from `(Main, nx) = (Main, n)` `n \<noteq> Entry` have "nx \<noteq> Entry" by simp
  with `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
  have "c\<^isub>1;;prog \<turnstile> nx \<oplus> #:c\<^isub>1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx' \<oplus> #:c\<^isub>1"
    by(rule Proc_CFG_edge_SeqSecond_source_not_Entry)
  with MainCallReturn show ?case by(fastsimp intro:PCFG.MainCallReturn)
qed (auto simp:intra_kind_def)


lemma valid_node_Main_SeqSecond:
  assumes "CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)"
  and "n \<noteq> Entry" and "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (c\<^isub>1;;prog,procs)"
  shows "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> #:c\<^isub>1)"
proof -
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` `Rep_wf_prog wfp' = (c\<^isub>1;;prog,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)`
  obtain a where "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    and "(Main,n) = sourcenode a \<or> (Main,n) = targetnode a"
    by(fastsimp simp:ProcCFG.valid_node_def valid_edge_def)
  from this `n \<noteq> Entry` wf show ?thesis
  proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
    case (Main nx et nx')
    from `(Main,n) = sourcenode a \<or> (Main,n) = targetnode a` show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with `(Main, nx) = sourcenode a`[THEN sym] have [simp]:"nx = n" by simp
      from `n \<noteq> Entry` `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'`
      have "c\<^isub>1;;prog \<turnstile> n \<oplus> #:c\<^isub>1 -IEdge et\<rightarrow>\<^isub>p nx' \<oplus> #:c\<^isub>1"
	by(fastsimp intro:Proc_CFG_edge_SeqSecond_source_not_Entry)
      hence "c\<^isub>1;;prog,procs \<turnstile> (Main,n \<oplus> #:c\<^isub>1) -et\<rightarrow> (Main,nx' \<oplus> #:c\<^isub>1)"
	by(rule PCFG.Main)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      show ?thesis
      proof(cases "nx = Entry")
	case True
	with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'` 
	have "nx' = Exit \<or> nx' = Label 0" by(fastsimp dest:Proc_CFG_EntryD)
	thus ?thesis
	proof
	  assume "nx' = Exit"
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis by simp
	next
	  assume "nx' = Label 0"
	  obtain l etx where "c\<^isub>1 \<turnstile> Label l -IEdge etx\<rightarrow>\<^isub>p Exit" and "l \<le> #:c\<^isub>1"
	    by(erule Proc_CFG_Exit_edge)
	  hence "c\<^isub>1;;prog \<turnstile> Label l -IEdge etx\<rightarrow>\<^isub>p Label #:c\<^isub>1"
	    by(fastsimp intro:Proc_CFG_SeqConnect)
	  with `nx' = Label 0` 
	  have "c\<^isub>1;;prog,procs \<turnstile> (Main,Label l) -etx\<rightarrow> (Main,nx'\<oplus>#:c\<^isub>1)"
	    by(fastsimp intro:PCFG.Main)
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis
	    by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
	qed
      next
	case False
	with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'`
	have "c\<^isub>1;;prog \<turnstile> nx \<oplus> #:c\<^isub>1 -IEdge et\<rightarrow>\<^isub>p nx' \<oplus> #:c\<^isub>1"
	  by(fastsimp intro:Proc_CFG_edge_SeqSecond_source_not_Entry)
	hence "c\<^isub>1;;prog,procs \<turnstile> (Main,nx \<oplus> #:c\<^isub>1) -et\<rightarrow> (Main,nx' \<oplus> #:c\<^isub>1)"
	  by(rule PCFG.Main)
	with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	show ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
      qed
    qed
  next
    case (Proc p ins outs c nx et n' es rets)
    from Proc(7)[THEN sym] Proc(9)[THEN sym] Proc(1-6) have False by fastsimp
    thus ?case by simp
  next
    case (MainCall l p es rets n' ins outs c)
    from `(p, ins, outs, c) \<in> set procs` wf `(p, Entry) = targetnode a`[THEN sym]
      `(Main, Label l) = sourcenode a`[THEN sym]
      `(Main, n) = sourcenode a \<or> (Main, n) = targetnode a`
     have [simp]:"n = Label l" by fastsimp
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'`
    have "c\<^isub>1;;prog \<turnstile> Label l \<oplus> #:c\<^isub>1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p n' \<oplus> #:c\<^isub>1"
      by -(rule Proc_CFG_edge_SeqSecond_source_not_Entry,auto)
    with `(p, ins, outs, c) \<in> set procs` `distinct rets`
      `length rets = length outs` `length es + 2 = length ins`
    have "c\<^isub>1;;prog,procs \<turnstile> (Main,Label (l + #:c\<^isub>1)) 
      -(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc (l + #:c\<^isub>1)) es\<rightarrow> (p,Entry)"
      by(fastsimp intro:PCFG.MainCall)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
  next
    case (ProcCall i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
    from ProcCall(12)[THEN sym] ProcCall(14)[THEN sym] ProcCall(1-11)
    have False by fastsimp
    thus ?case by simp
  next
    case (MainReturn l p es rets l' ins outs c)
    from `(p, ins, outs, c) \<in> set procs` wf `(p, Exit) = sourcenode a`[THEN sym]
      `(Main, Label l') = targetnode a`[THEN sym]
      `(Main, n) = sourcenode a \<or> (Main, n) = targetnode a`
    have [simp]:"n = Label l'" by fastsimp
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p Label l'`
    have "c\<^isub>1;;prog \<turnstile> Label l \<oplus> #:c\<^isub>1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p Label l' \<oplus> #:c\<^isub>1"
      by -(rule Proc_CFG_edge_SeqSecond_source_not_Entry,auto)
    with `(p, ins, outs, c) \<in> set procs` `distinct rets`
      `length rets = length outs` `length es + 2 = length ins`
    have "c\<^isub>1;;prog,procs \<turnstile> (p,Exit) -(correct_return 0 (l' + #:c\<^isub>1))\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs))\<rightarrow> (Main,Label (l' + #:c\<^isub>1))"
      by(fastsimp intro:PCFG.MainReturn)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
  next
    case (ProcReturn i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
    from ProcReturn(12)[THEN sym] ProcReturn(14)[THEN sym] ProcReturn(1-11)
    have False by fastsimp
    thus ?case by simp
  next
    case (MainCallReturn nx p es rets nx')
    from `(Main,n) = sourcenode a \<or> (Main,n) = targetnode a` show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with `(Main, nx) = sourcenode a`[THEN sym] have [simp]:"nx = n" by simp
      from `n \<noteq> Entry` `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "c\<^isub>1;;prog \<turnstile> n \<oplus> #:c\<^isub>1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx' \<oplus> #:c\<^isub>1"
	by(fastsimp intro:Proc_CFG_edge_SeqSecond_source_not_Entry)
      with `distinct rets`
      have "c\<^isub>1;;prog,procs \<turnstile> (Main,n \<oplus> #:c\<^isub>1) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> #:c\<^isub>1)"
	by -(rule PCFG.MainCallReturn)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      from `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "nx \<noteq> Entry" by(fastsimp dest:Proc_CFG_Call_Labels)
      with `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "c\<^isub>1;;prog \<turnstile> nx \<oplus> #:c\<^isub>1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx' \<oplus> #:c\<^isub>1"
	by(fastsimp intro:Proc_CFG_edge_SeqSecond_source_not_Entry)
      with `distinct rets`
      have "c\<^isub>1;;prog,procs \<turnstile> (Main,nx \<oplus> #:c\<^isub>1) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> #:c\<^isub>1)"
	by -(rule PCFG.MainCallReturn)
      with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym] 
      show ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    qed
  next
    case (ProcCallReturn p ins outs c nx p' es' rets' n' es rets)
    from ProcCallReturn(8)[THEN sym] ProcCallReturn(10)[THEN sym]
      ProcCallReturn(1-7) have False by fastsimp
    thus ?case by simp
  qed
qed


lemma path_Main_SeqSecond:
  assumes "Rep_wf_prog wfp = (prog,procs)" and "Rep_wf_prog wfp' = (c\<^isub>1;;prog,procs)"
  shows "\<lbrakk>wfp \<turnstile> (Main,n) -as\<rightarrow>* (p',n'); \<forall>a \<in> set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk>
  \<Longrightarrow> wfp' \<turnstile> (Main,n \<oplus> #:c\<^isub>1) -as \<oplus>s #:c\<^isub>1\<rightarrow>* (p',n' \<oplus> #:c\<^isub>1)"
proof(induct x\<equiv>"(Main,n)" as x'\<equiv>"(p',n')" arbitrary:n rule:ProcCFG.path.induct)
  case (empty_path m)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) m`
    `m = (Main, n)` `n \<noteq> Entry` `Rep_wf_prog wfp = (prog,procs)` 
    `Rep_wf_prog wfp' = (c\<^isub>1;;prog,procs)`
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> #:c\<^isub>1)"
    by(fastsimp intro:valid_node_Main_SeqSecond)
  with `m = (Main, n)` `m = (p', n')` show ?case
    by(fastsimp intro:ProcCFG.empty_path simp:label_incrs_def)
next
  case (Cons_path n'' as nx' a n nx)
  note IH = `\<And>n.  \<lbrakk>\<forall>a\<in>set as. intra_kind (kind a); n \<noteq> Entry; n'' = (Main, n);
    nx' = (p', n')\<rbrakk> \<Longrightarrow> wfp' \<turnstile> (Main, n \<oplus> #:c\<^isub>1) -as \<oplus>s #:c\<^isub>1\<rightarrow>* (p', n' \<oplus> #:c\<^isub>1)`
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` `Rep_wf_prog wfp' = (c\<^isub>1;;prog,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `\<forall>a\<in>set (a # as). intra_kind (kind a)` have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from `valid_edge wfp a` `sourcenode a = n` `targetnode a = n''`
    `intra_kind (kind a)` `n = (Main, nx)` wf 
  obtain nx'' where "n'' = (Main,nx'')" and "nx'' \<noteq> Entry"
    by(auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF `\<forall>a\<in>set as. intra_kind (kind a)` `nx'' \<noteq> Entry` `n'' = (Main,nx'')`
    `nx' = (p', n')`]
  have path:"wfp' \<turnstile> (Main, nx'' \<oplus> #:c\<^isub>1) -as \<oplus>s #:c\<^isub>1\<rightarrow>* (p', n' \<oplus> #:c\<^isub>1)" .
  from `valid_edge wfp a` `sourcenode a = n` `targetnode a = n''`
    `n = (Main, nx)` `n'' = (Main,nx'')` `nx \<noteq> Entry` `intra_kind (kind a)` wf
  have "c\<^isub>1;; prog,procs \<turnstile> (Main, nx\<oplus>#:c\<^isub>1) -kind a\<rightarrow> (Main, nx''\<oplus>#:c\<^isub>1)"
    by(fastsimp intro:PCFG_Main_edge_SeqSecond_source_not_Entry simp:valid_edge_def)
  with path `sourcenode a = n` `targetnode a = n''` `n = (Main, nx)` 
    `n'' = (Main,nx'')` show ?case
    apply(cases a) apply(clarsimp simp:label_incrs_def)
    by(auto intro:ProcCFG.Cons_path simp:valid_edge_def)
qed


subsubsection {* From @{text prog} to @{text "if (b) prog else c\<^isub>2"} *}

lemma Proc_CFG_edge_CondTrue_source_not_Entry:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^isub>p n'; n \<noteq> Entry\<rbrakk> \<Longrightarrow> if (b) prog else c\<^isub>2 \<turnstile> n \<oplus> 1 -et\<rightarrow>\<^isub>p n' \<oplus> 1"
by(induct rule:Proc_CFG.induct)(fastsimp intro:Proc_CFG_CondThen Proc_CFG.intros)+


lemma PCFG_Main_edge_CondTrue_source_not_Entry:
  "\<lbrakk>prog,procs \<turnstile> (Main,n) -et\<rightarrow> (p',n'); n \<noteq> Entry; intra_kind et; well_formed procs\<rbrakk>
  \<Longrightarrow> if (b) prog else c\<^isub>2,procs \<turnstile> (Main,n \<oplus> 1) -et\<rightarrow> (p',n' \<oplus> 1)"
proof(induct x\<equiv>"(Main,n)" et x'\<equiv>"(p',n')" rule:PCFG.induct)
  case Main
  thus ?case by(fastsimp dest:Proc_CFG_edge_CondTrue_source_not_Entry intro:PCFG.Main)
next
  case (MainCallReturn nx p es rets nx')
  from `(Main, nx) = (Main, n)` `n \<noteq> Entry` have "nx \<noteq> Entry" by simp
  with `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
  have "if (b) prog else c\<^isub>2 \<turnstile> nx \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx' \<oplus> 1"
    by(rule Proc_CFG_edge_CondTrue_source_not_Entry)
  with MainCallReturn show ?case by(fastsimp intro:PCFG.MainCallReturn)
qed (auto simp:intra_kind_def)


lemma valid_node_Main_CondTrue:
  assumes "CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)"
  and "n \<noteq> Entry" and "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (if (b) prog else c\<^isub>2,procs)"
  shows "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> 1)"
proof -
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` 
    `Rep_wf_prog wfp' = (if (b) prog else c\<^isub>2,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)`
  obtain a where "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    and "(Main,n) = sourcenode a \<or> (Main,n) = targetnode a"
    by(fastsimp simp:ProcCFG.valid_node_def valid_edge_def)
  from this `n \<noteq> Entry` wf show ?thesis
  proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
    case (Main nx et nx')
    from `(Main,n) = sourcenode a \<or> (Main,n) = targetnode a` show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with `(Main, nx) = sourcenode a`[THEN sym] have [simp]:"nx = n" by simp
      from `n \<noteq> Entry` `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'`
      have "if (b) prog else c\<^isub>2 \<turnstile> n \<oplus> 1 -IEdge et\<rightarrow>\<^isub>p nx' \<oplus> 1"
	by(fastsimp intro:Proc_CFG_edge_CondTrue_source_not_Entry)
      hence "if (b) prog else c\<^isub>2,procs \<turnstile> (Main,n \<oplus> 1) -et\<rightarrow> (Main,nx' \<oplus> 1)"
	by(rule PCFG.Main)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      show ?thesis
      proof(cases "nx = Entry")
	case True
	with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'` 
	have "nx' = Exit \<or> nx' = Label 0" by(fastsimp dest:Proc_CFG_EntryD)
	thus ?thesis
	proof
	  assume "nx' = Exit"
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis by simp
	next
	  assume "nx' = Label 0"
	  have "if (b) prog else c\<^isub>2 \<turnstile> Label 0 
	    -IEdge (\<lambda>cf. state_check cf b (Some true))\<^isub>\<surd>\<rightarrow>\<^isub>p Label 1"
	    by(rule Proc_CFG_CondTrue)
	  with `nx' = Label 0` 
	  have "if (b) prog else c\<^isub>2,procs \<turnstile> (Main,Label 0) 
	    -(\<lambda>cf. state_check cf b (Some true))\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> 1)" 
	    by(fastsimp intro:PCFG.Main)
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis
	    by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
	qed
      next
	case False
	with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'`
	have "if (b) prog else c\<^isub>2 \<turnstile> nx \<oplus> 1 -IEdge et\<rightarrow>\<^isub>p nx' \<oplus> 1"
	  by(fastsimp intro:Proc_CFG_edge_CondTrue_source_not_Entry)
	hence "if (b) prog else c\<^isub>2,procs \<turnstile> (Main,nx \<oplus> 1) -et\<rightarrow> 
	  (Main,nx' \<oplus> 1)" by(rule PCFG.Main)
	with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	show ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
      qed
    qed
  next
    case (Proc p ins outs c nx et n' es rets)
    from Proc(7)[THEN sym] Proc(9)[THEN sym] Proc(1-6) have False by fastsimp
    thus ?case by simp
  next
    case (MainCall l p es rets n' ins outs c)
    from `(p, ins, outs, c) \<in> set procs` `(p, Entry) = targetnode a`[THEN sym] 
      `(Main, Label l) = sourcenode a`[THEN sym] wf
      `(Main, n) = sourcenode a \<or> (Main, n) = targetnode a`
    have [simp]:"n = Label l" by fastsimp
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'`
    have "if (b) prog else c\<^isub>2 \<turnstile> Label l \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p n' \<oplus> 1"
      by -(rule Proc_CFG_edge_CondTrue_source_not_Entry,auto)
    with `(p, ins, outs, c) \<in> set procs` `distinct rets`
      `length rets = length outs` `length es + 2 = length ins`
    have "if (b) prog else c\<^isub>2,procs \<turnstile> (Main,Label (l + 1)) 
      -(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc (l + 1)) es\<rightarrow> (p,Entry)"
      by(fastsimp intro:PCFG.MainCall)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
  next
    case (ProcCall i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
    from ProcCall(12)[THEN sym] ProcCall(14)[THEN sym] ProcCall(1-11)
    have False by fastsimp
    thus ?case by simp
  next
    case (MainReturn l p es rets l' ins outs c)
    from `(p, ins, outs, c) \<in> set procs` `(p, Exit) = sourcenode a`[THEN sym] 
      `(Main, Label l') = targetnode a`[THEN sym] wf
      `(Main, n) = sourcenode a \<or> (Main, n) = targetnode a`
    have [simp]:"n = Label l'" by fastsimp
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p Label l'`
    have "if (b) prog else c\<^isub>2 \<turnstile> Label l \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p Label l' \<oplus> 1"
      by -(rule Proc_CFG_edge_CondTrue_source_not_Entry,auto)
    with `(p, ins, outs, c) \<in> set procs` `distinct rets`
      `length rets = length outs` `length es + 2 = length ins`
    have "if (b) prog else c\<^isub>2,procs \<turnstile> (p,Exit) -(correct_return 0 (l' + 1))\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs))\<rightarrow> (Main,Label (l' + 1))"
      by(fastsimp intro:PCFG.MainReturn)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
  next
    case (ProcReturn i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
    from ProcReturn(12)[THEN sym] ProcReturn(14)[THEN sym] ProcReturn(1-11)
    have False by fastsimp
    thus ?case by simp
  next
    case (MainCallReturn nx p es rets nx')
    from `(Main,n) = sourcenode a \<or> (Main,n) = targetnode a` show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with `(Main, nx) = sourcenode a`[THEN sym] have [simp]:"nx = n" by simp
      from `n \<noteq> Entry` `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "if (b) prog else c\<^isub>2 \<turnstile> n \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx' \<oplus> 1"
	by(fastsimp intro:Proc_CFG_edge_CondTrue_source_not_Entry)
      with `distinct rets`
      have "if (b) prog else c\<^isub>2,procs \<turnstile> (Main,n \<oplus> 1) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> 
	(Main,nx' \<oplus> 1)" by -(rule PCFG.MainCallReturn)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      from `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "nx \<noteq> Entry" by(fastsimp dest:Proc_CFG_Call_Labels)
      with `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "if (b) prog else c\<^isub>2 \<turnstile> nx \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx' \<oplus> 1"
	by(fastsimp intro:Proc_CFG_edge_CondTrue_source_not_Entry)
      with `distinct rets`
      have "if (b) prog else c\<^isub>2,procs \<turnstile> (Main,nx \<oplus> 1) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> 1)"
	by -(rule PCFG.MainCallReturn)
      with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
      show ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    qed
  next
    case (ProcCallReturn p ins outs c nx p' es' rets' n' es rets)
    from ProcCallReturn(8)[THEN sym] ProcCallReturn(10)[THEN sym]
      ProcCallReturn(1-7) have False by fastsimp
    thus ?case by simp
  qed
qed


lemma path_Main_CondTrue:
  assumes "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (if (b) prog else c\<^isub>2,procs)"
  shows "\<lbrakk>wfp \<turnstile> (Main,n) -as\<rightarrow>* (p',n'); \<forall>a \<in> set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk>
  \<Longrightarrow> wfp' \<turnstile> (Main,n \<oplus> 1) -as \<oplus>s 1\<rightarrow>* (p',n' \<oplus> 1)"
proof(induct x\<equiv>"(Main,n)" as x'\<equiv>"(p',n')" arbitrary:n rule:ProcCFG.path.induct)
  case (empty_path m)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) m`
    `m = (Main, n)` `n \<noteq> Entry` `Rep_wf_prog wfp = (prog,procs)` 
    `Rep_wf_prog wfp' = (if (b) prog else c\<^isub>2,procs)`
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> 1)" 
    by(fastsimp intro:valid_node_Main_CondTrue)
  with `m = (Main, n)` `m = (p', n')` show ?case
    by(fastsimp intro:ProcCFG.empty_path simp:label_incrs_def)
next
  case (Cons_path n'' as nx' a n nx)
  note IH = `\<And>n.  \<lbrakk>\<forall>a\<in>set as. intra_kind (kind a); n \<noteq> Entry; n'' = (Main, n);
    nx' = (p', n')\<rbrakk> \<Longrightarrow> wfp' \<turnstile> (Main, n \<oplus> 1) -as \<oplus>s 1\<rightarrow>* (p', n' \<oplus> 1)`
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` 
    `Rep_wf_prog wfp' = (if (b) prog else c\<^isub>2,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `\<forall>a\<in>set (a # as). intra_kind (kind a)` have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from `valid_edge wfp a` `sourcenode a = n` `targetnode a = n''`
    `intra_kind (kind a)` `n = (Main, nx)` wf 
  obtain nx'' where "n'' = (Main,nx'')" and "nx'' \<noteq> Entry"
    by(auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF `\<forall>a\<in>set as. intra_kind (kind a)` `nx'' \<noteq> Entry` `n'' = (Main,nx'')`
    `nx' = (p', n')`] have path:"wfp' \<turnstile> (Main, nx'' \<oplus> 1) -as \<oplus>s 1\<rightarrow>* (p', n' \<oplus> 1)" .
  from `valid_edge wfp a` `sourcenode a = n` `targetnode a = n''`
    `n = (Main, nx)` `n'' = (Main,nx'')` `nx \<noteq> Entry` `intra_kind (kind a)` wf
  have "if (b) prog else c\<^isub>2,procs \<turnstile> (Main, nx \<oplus> 1) -kind a\<rightarrow> (Main, nx'' \<oplus> 1)"
    by(fastsimp intro:PCFG_Main_edge_CondTrue_source_not_Entry simp:valid_edge_def)
  with path `sourcenode a = n` `targetnode a = n''` `n = (Main, nx)` 
    `n'' = (Main,nx'')` show ?case
    apply(cases a) apply(clarsimp simp:label_incrs_def)
    by(auto intro:ProcCFG.Cons_path simp:valid_edge_def)
qed


subsubsection {* From @{text prog} to @{text "if (b) c\<^isub>1 else prog"} *}

lemma Proc_CFG_edge_CondFalse_source_not_Entry:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^isub>p n'; n \<noteq> Entry\<rbrakk> 
  \<Longrightarrow> if (b) c\<^isub>1 else prog \<turnstile> n \<oplus> (#:c\<^isub>1 + 1) -et\<rightarrow>\<^isub>p n' \<oplus> (#:c\<^isub>1 + 1)"
by(induct rule:Proc_CFG.induct)(fastsimp intro:Proc_CFG_CondElse Proc_CFG.intros)+


lemma PCFG_Main_edge_CondFalse_source_not_Entry:
  "\<lbrakk>prog,procs \<turnstile> (Main,n) -et\<rightarrow> (p',n'); n \<noteq> Entry; intra_kind et; well_formed procs\<rbrakk>
  \<Longrightarrow> if (b) c\<^isub>1 else prog,procs \<turnstile> (Main,n \<oplus> (#:c\<^isub>1 + 1)) -et\<rightarrow> (p',n' \<oplus> (#:c\<^isub>1 + 1))"
proof(induct x\<equiv>"(Main,n)" et x'\<equiv>"(p',n')" rule:PCFG.induct)
  case Main
  thus ?case 
    by(fastsimp dest:Proc_CFG_edge_CondFalse_source_not_Entry intro:PCFG.Main)
next
  case (MainCallReturn nx p es rets nx')
  from `(Main, nx) = (Main, n)` `n \<noteq> Entry` have "nx \<noteq> Entry" by simp
  with `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
  have "if (b) c\<^isub>1 else prog \<turnstile> nx \<oplus> (#:c\<^isub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx' \<oplus> (#:c\<^isub>1 + 1)"
    by(rule Proc_CFG_edge_CondFalse_source_not_Entry)
  with MainCallReturn show ?case by(fastsimp intro:PCFG.MainCallReturn)
qed (auto simp:intra_kind_def)


lemma valid_node_Main_CondFalse:
  assumes "CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)"
  and "n \<noteq> Entry" and "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (if (b) c\<^isub>1 else prog,procs)"
  shows "CFG.valid_node sourcenode targetnode (valid_edge wfp') 
  (Main, n \<oplus> (#:c\<^isub>1 + 1))"
proof -
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` 
    `Rep_wf_prog wfp' = (if (b) c\<^isub>1 else prog,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)`
  obtain a where "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    and "(Main,n) = sourcenode a \<or> (Main,n) = targetnode a"
    by(fastsimp simp:ProcCFG.valid_node_def valid_edge_def)
  from this `n \<noteq> Entry` wf show ?thesis
  proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
    case (Main nx et nx')
    from `(Main,n) = sourcenode a \<or> (Main,n) = targetnode a` show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with `(Main, nx) = sourcenode a`[THEN sym] have [simp]:"nx = n" by simp
      from `n \<noteq> Entry` `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'`
      have "if (b) c\<^isub>1 else prog \<turnstile> n \<oplus> (#:c\<^isub>1 + 1) -IEdge et\<rightarrow>\<^isub>p nx' \<oplus> (#:c\<^isub>1 + 1)"
	by(fastsimp intro:Proc_CFG_edge_CondFalse_source_not_Entry)
      hence "if (b) c\<^isub>1 else prog,procs \<turnstile> (Main,n \<oplus> (#:c\<^isub>1 + 1)) -et\<rightarrow> 
	(Main,nx' \<oplus> (#:c\<^isub>1 + 1))" by(rule PCFG.Main)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      show ?thesis
      proof(cases "nx = Entry")
	case True
	with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'` 
	have "nx' = Exit \<or> nx' = Label 0" by(fastsimp dest:Proc_CFG_EntryD)
	thus ?thesis
	proof
	  assume "nx' = Exit"
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis by simp
	next
	  assume "nx' = Label 0"
	  have "if (b) c\<^isub>1 else prog \<turnstile> Label 0 
	    -IEdge (\<lambda>cf. state_check cf b (Some false))\<^isub>\<surd>\<rightarrow>\<^isub>p Label (#:c\<^isub>1 + 1)"
	    by(rule Proc_CFG_CondFalse)
	  with `nx' = Label 0` 
	  have "if (b) c\<^isub>1 else prog,procs \<turnstile> (Main,Label 0) 
	    -(\<lambda>cf. state_check cf b (Some false))\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> (#:c\<^isub>1 + 1))" 
	    by(fastsimp intro:PCFG.Main)
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis
	    by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
	qed
      next
	case False
	with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'`
	have "if (b) c\<^isub>1 else prog \<turnstile> nx \<oplus> (#:c\<^isub>1 + 1) -IEdge et\<rightarrow>\<^isub>p nx' \<oplus> (#:c\<^isub>1 + 1)"
	  by(fastsimp intro:Proc_CFG_edge_CondFalse_source_not_Entry)
	hence "if (b) c\<^isub>1 else prog,procs \<turnstile> (Main,nx \<oplus> (#:c\<^isub>1 + 1)) 
	  -et\<rightarrow> (Main,nx' \<oplus> (#:c\<^isub>1 + 1))" by(rule PCFG.Main)
	with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym] 
	show ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
      qed
    qed
  next
    case (Proc p ins outs c nx et n' es rets)
    from Proc(7)[THEN sym] Proc(9)[THEN sym] Proc(1-6) have False by fastsimp
    thus ?case by simp
  next
    case (MainCall l p es rets n' ins outs c)
    from `(p, ins, outs, c) \<in> set procs` `(p, Entry) = targetnode a`[THEN sym]
      `(Main, Label l) = sourcenode a`[THEN sym] wf
      `(Main, n) = sourcenode a \<or> (Main, n) = targetnode a`
    have [simp]:"n = Label l" by fastsimp
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'`
    have "if (b) c\<^isub>1 else prog \<turnstile> Label l \<oplus> (#:c\<^isub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^isub>p 
      n' \<oplus> (#:c\<^isub>1 + 1)" by -(rule Proc_CFG_edge_CondFalse_source_not_Entry,auto)
    with `(p, ins, outs, c) \<in> set procs` `distinct rets`
      `length rets = length outs` `length es + 2 = length ins`
    have "if (b) c\<^isub>1 else prog,procs \<turnstile> (Main,Label (l + (#:c\<^isub>1 + 1))) 
      -(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc (l + (#:c\<^isub>1 + 1))) es\<rightarrow> (p,Entry)"
      by(fastsimp intro:PCFG.MainCall)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
  next
    case (ProcCall i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
    from ProcCall(12)[THEN sym] ProcCall(14)[THEN sym] ProcCall(1-11)
    have False by fastsimp
    thus ?case by simp
  next
    case (MainReturn l p es rets l' ins outs c)
    from `(p, ins, outs, c) \<in> set procs` `(p, Exit) = sourcenode a`[THEN sym]
      `(Main, Label l') = targetnode a`[THEN sym] wf
      `(Main, n) = sourcenode a \<or> (Main, n) = targetnode a`
    have [simp]:"n = Label l'" by fastsimp
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p Label l'`
    have "if (b) c\<^isub>1 else prog \<turnstile> Label l \<oplus> (#:c\<^isub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^isub>p 
      Label l' \<oplus> (#:c\<^isub>1 + 1)" by -(rule Proc_CFG_edge_CondFalse_source_not_Entry,auto)
    with `(p, ins, outs, c) \<in> set procs` `distinct rets`
      `length rets = length outs` `length es + 2 = length ins`
    have "if (b) c\<^isub>1 else prog,procs \<turnstile> (p,Exit) 
      -(correct_return 0 (l' + (#:c\<^isub>1 + 1)))\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs))\<rightarrow> (Main,Label (l' + (#:c\<^isub>1 + 1)))"
      by(fastsimp intro:PCFG.MainReturn)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
  next
    case (ProcReturn i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
    from ProcReturn(12)[THEN sym] ProcReturn(14)[THEN sym] ProcReturn(1-11)
    have False by fastsimp
    thus ?case by simp
  next
    case (MainCallReturn nx p es rets nx')
    from `(Main,n) = sourcenode a \<or> (Main,n) = targetnode a` show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with `(Main, nx) = sourcenode a`[THEN sym] have [simp]:"nx = n" by simp
      from `n \<noteq> Entry` `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "if (b) c\<^isub>1 else prog \<turnstile> n \<oplus> (#:c\<^isub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^isub>p 
	nx' \<oplus> (#:c\<^isub>1 + 1)" by(fastsimp intro:Proc_CFG_edge_CondFalse_source_not_Entry)
      with `distinct rets`
      have "if (b) c\<^isub>1 else prog,procs \<turnstile> (Main,n \<oplus> (#:c\<^isub>1 + 1)) 
	-(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> (#:c\<^isub>1 + 1))" by -(rule PCFG.MainCallReturn)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      from `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "nx \<noteq> Entry" by(fastsimp dest:Proc_CFG_Call_Labels)
      with `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "if (b) c\<^isub>1 else prog \<turnstile> nx \<oplus> (#:c\<^isub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^isub>p 
	nx' \<oplus> (#:c\<^isub>1 + 1)" by(fastsimp intro:Proc_CFG_edge_CondFalse_source_not_Entry)
      with `distinct rets`
      have "if (b) c\<^isub>1 else prog,procs \<turnstile> (Main,nx \<oplus> (#:c\<^isub>1 + 1)) 
	-(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> (#:c\<^isub>1 + 1))" by -(rule PCFG.MainCallReturn)
      with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
      show ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    qed
  next
    case (ProcCallReturn p ins outs c nx p' es' rets' n' es rets)
    from ProcCallReturn(8)[THEN sym] ProcCallReturn(10)[THEN sym]
      ProcCallReturn(1-7) have False by fastsimp
    thus ?case by simp
  qed
qed


lemma path_Main_CondFalse:
  assumes "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (if (b) c\<^isub>1 else prog,procs)"
  shows "\<lbrakk>wfp \<turnstile> (Main,n) -as\<rightarrow>* (p',n'); \<forall>a \<in> set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk>
  \<Longrightarrow> wfp' \<turnstile> (Main,n \<oplus> (#:c\<^isub>1 + 1)) -as \<oplus>s (#:c\<^isub>1 + 1)\<rightarrow>* (p',n' \<oplus> (#:c\<^isub>1 + 1))"
proof(induct x\<equiv>"(Main,n)" as x'\<equiv>"(p',n')" arbitrary:n rule:ProcCFG.path.induct)
  case (empty_path m)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) m`
    `m = (Main, n)` `n \<noteq> Entry` `Rep_wf_prog wfp = (prog,procs)` 
    `Rep_wf_prog wfp' = (if (b) c\<^isub>1 else prog,procs)`
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> (#:c\<^isub>1 + 1))"
    by(fastsimp intro:valid_node_Main_CondFalse)
  with `m = (Main, n)` `m = (p', n')` show ?case
    by(fastsimp intro:ProcCFG.empty_path simp:label_incrs_def)
next
  case (Cons_path n'' as nx' a n nx)
  note IH = `\<And>n.  \<lbrakk>\<forall>a\<in>set as. intra_kind (kind a); n \<noteq> Entry; n'' = (Main, n);
    nx' = (p', n')\<rbrakk>
    \<Longrightarrow> wfp' \<turnstile> (Main, n \<oplus> (#:c\<^isub>1 + 1)) -as \<oplus>s (#:c\<^isub>1 + 1)\<rightarrow>* (p', n' \<oplus> (#:c\<^isub>1 + 1))`
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` 
    `Rep_wf_prog wfp' = (if (b) c\<^isub>1 else prog,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `\<forall>a\<in>set (a # as). intra_kind (kind a)` have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from `valid_edge wfp a` `sourcenode a = n` `targetnode a = n''`
    `intra_kind (kind a)` `n = (Main, nx)` wf 
  obtain nx'' where "n'' = (Main,nx'')" and "nx'' \<noteq> Entry"
    by(auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF `\<forall>a\<in>set as. intra_kind (kind a)` `nx'' \<noteq> Entry` `n'' = (Main,nx'')`
    `nx' = (p', n')`] have path:"wfp' \<turnstile> (Main, nx'' \<oplus> (#:c\<^isub>1 + 1)) 
    -as \<oplus>s (#:c\<^isub>1 + 1)\<rightarrow>* (p', n' \<oplus> (#:c\<^isub>1 + 1))" .
  from `valid_edge wfp a` `sourcenode a = n` `targetnode a = n''`
    `n = (Main, nx)` `n'' = (Main,nx'')` `nx \<noteq> Entry` `intra_kind (kind a)` wf
  have "if (b) c\<^isub>1 else prog,procs \<turnstile> (Main, nx \<oplus> (#:c\<^isub>1 + 1)) -kind a\<rightarrow> 
    (Main, nx'' \<oplus> (#:c\<^isub>1 + 1))"
    by(fastsimp intro:PCFG_Main_edge_CondFalse_source_not_Entry simp:valid_edge_def)
  with path `sourcenode a = n` `targetnode a = n''` `n = (Main, nx)` 
    `n'' = (Main,nx'')` show ?case
    apply(cases a) apply(clarsimp simp:label_incrs_def)
    by(auto intro:ProcCFG.Cons_path simp:valid_edge_def)
qed


subsubsection {* From @{text prog} to @{text "while (b) prog"} *}

lemma Proc_CFG_edge_WhileBody_source_not_Entry:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^isub>p n'; n \<noteq> Entry; n' \<noteq> Exit\<rbrakk> 
  \<Longrightarrow> while (b) prog \<turnstile> n \<oplus> 2 -et\<rightarrow>\<^isub>p n' \<oplus> 2"
by(induct rule:Proc_CFG.induct)(fastsimp intro:Proc_CFG_WhileBody Proc_CFG.intros)+


lemma PCFG_Main_edge_WhileBody_source_not_Entry:
  "\<lbrakk>prog,procs \<turnstile> (Main,n) -et\<rightarrow> (p',n'); n \<noteq> Entry; n' \<noteq> Exit; intra_kind et; 
  well_formed procs\<rbrakk> \<Longrightarrow> while (b) prog,procs \<turnstile> (Main,n \<oplus> 2) -et\<rightarrow> (p',n' \<oplus> 2)"
proof(induct x\<equiv>"(Main,n)" et x'\<equiv>"(p',n')" rule:PCFG.induct)
  case Main
  thus ?case 
    by(fastsimp dest:Proc_CFG_edge_WhileBody_source_not_Entry intro:PCFG.Main)
next
  case (MainCallReturn nx p es rets nx')
  from `(Main, nx) = (Main, n)` `n \<noteq> Entry` `(Main, nx') = (p', n')` `n' \<noteq> Exit`
  have "nx \<noteq> Entry" and "nx' \<noteq> Exit" by simp_all
  with `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
  have "while (b) prog \<turnstile> nx \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx' \<oplus> 2"
    by(rule Proc_CFG_edge_WhileBody_source_not_Entry)
  with MainCallReturn show ?case by(fastsimp intro:PCFG.MainCallReturn)
qed (auto simp:intra_kind_def)


lemma valid_node_Main_WhileBody:
  assumes "CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)"
  and "n \<noteq> Entry" and "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (while (b) prog,procs)"
  shows "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> 2)"
proof -
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` 
    `Rep_wf_prog wfp' = (while (b) prog,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)`
  obtain a where "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    and "(Main,n) = sourcenode a \<or> (Main,n) = targetnode a"
    by(fastsimp simp:ProcCFG.valid_node_def valid_edge_def)
  from this `n \<noteq> Entry` wf show ?thesis
  proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
    case (Main nx et nx')
    from `(Main,n) = sourcenode a \<or> (Main,n) = targetnode a` show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with `(Main, nx) = sourcenode a`[THEN sym] have [simp]:"nx = n" by simp
      show ?thesis
      proof(cases "nx' = Exit")
	case True
	with `n \<noteq> Entry` `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'`
	have "while (b) prog \<turnstile> n \<oplus> 2 -IEdge et\<rightarrow>\<^isub>p Label 0"
	  by(fastsimp intro:Proc_CFG_WhileBodyExit)
	hence "while (b) prog,procs \<turnstile> (Main,n \<oplus> 2) -et\<rightarrow> (Main,Label 0)"
	  by(rule PCFG.Main)
	thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
      next
	case False
	with `n \<noteq> Entry` `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'`
	have "while (b) prog \<turnstile> n \<oplus> 2 -IEdge et\<rightarrow>\<^isub>p nx' \<oplus> 2"
	  by(fastsimp intro:Proc_CFG_edge_WhileBody_source_not_Entry)
	hence "while (b) prog,procs \<turnstile> (Main,n \<oplus> 2) -et\<rightarrow> (Main,nx' \<oplus> 2)"
	  by(rule PCFG.Main)
	thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
      qed
    next
      assume "(Main, n) = targetnode a"
      show ?thesis
      proof(cases "nx = Entry")
	case True
	with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'` 
	have "nx' = Exit \<or> nx' = Label 0" by(fastsimp dest:Proc_CFG_EntryD)
	thus ?thesis
	proof
	  assume "nx' = Exit"
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis by simp
	next
	  assume "nx' = Label 0"
	  have "while (b) prog \<turnstile> Label 0 
	    -IEdge (\<lambda>cf. state_check cf b (Some true))\<^isub>\<surd>\<rightarrow>\<^isub>p Label 2"
	    by(rule Proc_CFG_WhileTrue)
	  hence "while (b) prog,procs \<turnstile> (Main,Label 0) 
	    -(\<lambda>cf. state_check cf b (Some true))\<^isub>\<surd>\<rightarrow> (Main,Label 2)"
	    by(fastsimp intro:PCFG.Main)
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	    `nx' = Label 0` show ?thesis
	    by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
	qed
      next
	case False
	show ?thesis
	proof(cases "nx' = Exit")
	  case True
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis by simp
	next
	  case False
	  with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'` `nx \<noteq> Entry`
	  have "while (b) prog \<turnstile> nx \<oplus> 2 -IEdge et\<rightarrow>\<^isub>p nx' \<oplus> 2"
	    by(fastsimp intro:Proc_CFG_edge_WhileBody_source_not_Entry)
	  hence "while (b) prog,procs \<turnstile> (Main,nx \<oplus> 2) 
	    -et\<rightarrow> (Main,nx' \<oplus> 2)" by(rule PCFG.Main)
	  with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym]
	  show ?thesis
	    by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
	qed
      qed
    qed
  next
    case (Proc p ins outs c nx et n' es rets)
    from Proc(7)[THEN sym] Proc(9)[THEN sym] Proc(1-6) have False by fastsimp
    thus ?case by simp
  next
    case (MainCall l p es rets n' ins outs c)
    from `(p, ins, outs, c) \<in> set procs` `(p, Entry) = targetnode a`[THEN sym]
      `(Main, Label l) = sourcenode a`[THEN sym] wf
      `(Main, n) = sourcenode a \<or> (Main, n) = targetnode a`
    have [simp]:"n = Label l" by fastsimp
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'` have "n' \<noteq> Exit"
      by(fastsimp dest:Proc_CFG_Call_Labels)
    with `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p n'`
    have "while (b) prog \<turnstile> Label l \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^isub>p 
      n' \<oplus> 2" by -(rule Proc_CFG_edge_WhileBody_source_not_Entry,auto)
    with `(p, ins, outs, c) \<in> set procs` `distinct rets`
      `length rets = length outs` `length es + 2 = length ins`
    have "while (b) prog,procs \<turnstile> (Main,Label (l + 2)) 
      -(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc (l + 2)) es\<rightarrow> (p,Entry)"
      by(fastsimp intro:PCFG.MainCall)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
  next
    case (ProcCall i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
    from ProcCall(12)[THEN sym] ProcCall(14)[THEN sym] ProcCall(1-11)
    have False by fastsimp
    thus ?case by simp
  next
    case (MainReturn l p es rets l' ins outs c)
    from `(p, ins, outs, c) \<in> set procs` `(p, Exit) = sourcenode a`[THEN sym]
      `(Main, Label l') = targetnode a`[THEN sym] wf
      `(Main, n) = sourcenode a \<or> (Main, n) = targetnode a`
    have [simp]:"n = Label l'" by fastsimp
    from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^isub>p Label l'`
    have "while (b) prog \<turnstile> Label l \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^isub>p 
      Label l' \<oplus> 2" by -(rule Proc_CFG_edge_WhileBody_source_not_Entry,auto)
    with `(p, ins, outs, c) \<in> set procs` `distinct rets`
      `length rets = length outs` `length es + 2 = length ins`
    have "while (b) prog,procs \<turnstile> (p,Exit) -(correct_return 0 (l' + 2))\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs))\<rightarrow> (Main,Label (l' + 2))"
      by(fastsimp intro:PCFG.MainReturn)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
  next
    case (ProcReturn i p ins outs c l p' es' rets' l' ins' outs' c' es rets)
    from ProcReturn(12)[THEN sym] ProcReturn(14)[THEN sym] ProcReturn(1-11)
    have False by fastsimp
    thus ?case by simp
  next
    case (MainCallReturn nx p es rets nx')
    from `(Main,n) = sourcenode a \<or> (Main,n) = targetnode a` show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with `(Main, nx) = sourcenode a`[THEN sym] have [simp]:"nx = n" by simp
      from `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'` have "nx' \<noteq> Exit"
	by(fastsimp dest:Proc_CFG_Call_Labels)
      with `n \<noteq> Entry` `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "while (b) prog \<turnstile> n \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^isub>p 
	nx' \<oplus> 2" by(fastsimp intro:Proc_CFG_edge_WhileBody_source_not_Entry)
      with `distinct rets`
      have "while (b) prog,procs \<turnstile> (Main,n \<oplus> 2) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> 2)"
	by -(rule PCFG.MainCallReturn)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      from `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "nx \<noteq> Entry" and "nx' \<noteq> Exit" by(auto dest:Proc_CFG_Call_Labels)
      with `prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^isub>p nx'`
      have "while (b) prog \<turnstile> nx \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^isub>p 
	nx' \<oplus> 2" by(fastsimp intro:Proc_CFG_edge_WhileBody_source_not_Entry)
      with `distinct rets`
      have "while (b) prog,procs \<turnstile> (Main,nx \<oplus> 2) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,nx' \<oplus> 2)"
	by -(rule PCFG.MainCallReturn)
      with `(Main, n) = targetnode a` `(Main, nx') = targetnode a`[THEN sym] 
      show ?thesis by(simp add:ProcCFG.valid_node_def)(fastsimp simp:valid_edge_def)
    qed
  next
    case (ProcCallReturn p ins outs c nx p' es' rets' n' es rets)
    from ProcCallReturn(8)[THEN sym] ProcCallReturn(10)[THEN sym]
      ProcCallReturn(1-7) have False by fastsimp
    thus ?case by simp
  qed
qed


lemma path_Main_WhileBody:
  assumes "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (while (b) prog,procs)"
  shows "\<lbrakk>wfp \<turnstile> (Main,n) -as\<rightarrow>* (p',n'); \<forall>a \<in> set as. intra_kind (kind a); 
    n \<noteq> Entry; n' \<noteq> Exit\<rbrakk> \<Longrightarrow> wfp' \<turnstile> (Main,n \<oplus> 2) -as \<oplus>s 2\<rightarrow>* (p',n' \<oplus> 2)"
proof(induct x\<equiv>"(Main,n)" as x'\<equiv>"(p',n')" arbitrary:n rule:ProcCFG.path.induct)
  case (empty_path m)
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp) m`
    `m = (Main, n)` `n \<noteq> Entry` `Rep_wf_prog wfp = (prog,procs)`
    `Rep_wf_prog wfp' = (while (b) prog,procs)`
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> 2)" 
    by(fastsimp intro:valid_node_Main_WhileBody)
  with `m = (Main, n)` `m = (p', n')` show ?case
    by(fastsimp intro:ProcCFG.empty_path simp:label_incrs_def)
next
  case (Cons_path n'' as nx' a n nx)
  note IH = `\<And>n.  \<lbrakk>\<forall>a\<in>set as. intra_kind (kind a); n \<noteq> Entry; n' \<noteq> Exit; 
    n'' = (Main, n); nx' = (p', n')\<rbrakk> \<Longrightarrow> wfp' \<turnstile> (Main, n \<oplus> 2) -as \<oplus>s 2\<rightarrow>* (p', n' \<oplus> 2)`
  note [simp] = `Rep_wf_prog wfp = (prog,procs)` 
     `Rep_wf_prog wfp' = (while (b) prog,procs)`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `\<forall>a\<in>set (a # as). intra_kind (kind a)` have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from `valid_edge wfp a` `sourcenode a = n` `targetnode a = n''`
    `intra_kind (kind a)` `n = (Main, nx)` wf 
  obtain nx'' where "n'' = (Main,nx'')" and "nx'' \<noteq> Entry"
    by(auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF `\<forall>a\<in>set as. intra_kind (kind a)` `nx'' \<noteq> Entry` `n' \<noteq> Exit` 
    `n'' = (Main,nx'')` `nx' = (p', n')`]
  have path:"wfp' \<turnstile> (Main, nx'' \<oplus> 2) -as \<oplus>s 2\<rightarrow>* (p', n' \<oplus> 2)" .
  with `n' \<noteq> Exit` have "nx'' \<noteq> Exit" by(fastsimp dest:ProcCFGExit.path_Exit_source)
  with `valid_edge wfp a` `sourcenode a = n` `targetnode a = n''`
    `n = (Main, nx)` `n'' = (Main,nx'')` `nx \<noteq> Entry` `intra_kind (kind a)` wf
  have "while (b) prog,procs \<turnstile> (Main, nx \<oplus> 2) -kind a\<rightarrow> (Main, nx'' \<oplus> 2)"
    by(fastsimp intro:PCFG_Main_edge_WhileBody_source_not_Entry simp:valid_edge_def)
  with path `sourcenode a = n` `targetnode a = n''` `n = (Main, nx)` 
    `n'' = (Main,nx'')` show ?case
    apply(cases a) apply(clarsimp simp:label_incrs_def)
    by(auto intro:ProcCFG.Cons_path simp:valid_edge_def)
qed


subsubsection {* Existence of intraprodecural paths *}

lemma Label_Proc_CFG_Entry_Exit_path_Main:
  assumes "Rep_wf_prog wfp = (prog,procs)" and "l < #:prog"
  obtains as as' where "wfp \<turnstile> (Main,Label l) -as\<rightarrow>* (Main,Exit)"
  and "\<forall>a \<in> set as. intra_kind (kind a)"
  and "wfp \<turnstile> (Main,Entry) -as'\<rightarrow>* (Main,Label l)"
  and "\<forall>a \<in> set as'. intra_kind (kind a)"
proof(atomize_elim)
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `l < #:prog` `Rep_wf_prog wfp = (prog,procs)`
  show "\<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and>
    (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
    wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))"
  proof(induct prog arbitrary:l wfp)
    case Skip
    note [simp] = `Rep_wf_prog wfp = (Skip, procs)`
    from `l < #:Skip` have [simp]:"l = 0" by simp
    have "wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))]\<rightarrow>* 
      (Main,Label 0)" 
      by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_Entry
                   simp:valid_edge_def ProcCFG.valid_node_def)
    moreover
    have "wfp \<turnstile> (Main,Label l) -[((Main,Label l),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)" 
      by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_Skip simp:valid_edge_def)
    ultimately show ?case by(fastsimp simp:intra_kind_def)
  next
    case (LAss V e)
    note [simp] = `Rep_wf_prog wfp = (V:=e, procs)`
    from `l < #:V:=e` have "l = 0 \<or> l = 1" by auto
    thus ?case
    proof
      assume [simp]:"l = 0"
      have "wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))]\<rightarrow>*
	(Main,Label 0)" 
	by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_Entry
       	            simp:valid_edge_def ProcCFG.valid_node_def)
      moreover
      have "wfp \<turnstile> (Main,Label 0) 
	-((Main,Label 0),\<Up>(\<lambda>cf. update cf V e),(Main,Label 1))#
	[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
	by(fastsimp intro:ProcCFG.Cons_path ProcCFG.path.intros Main Proc_CFG_LAss 
	  Proc_CFG_LAssSkip simp:valid_edge_def ProcCFG.valid_node_def)
      ultimately show ?thesis by(fastsimp simp:intra_kind_def)
    next
      assume [simp]:"l = 1"
      have "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))#
	[((Main,Label 0),\<Up>(\<lambda>cf. update cf V e),(Main,Label 1))]\<rightarrow>* (Main,Label 1)"
	by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_LAss ProcCFG.Cons_path 
	  Main Proc_CFG_Entry simp:ProcCFG.valid_node_def valid_edge_def)
      moreover
      have "wfp \<turnstile> (Main,Label 1) -[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* 
	(Main,Exit)" by(fastsimp intro:ProcCFG.path.intros  Main Proc_CFG_LAssSkip
	simp:valid_edge_def ProcCFG.valid_node_def)
      ultimately show ?thesis by(fastsimp simp:intra_kind_def)
    qed
  next
    case (Seq c\<^isub>1 c\<^isub>2)
    note IH1 = `\<And>l wfp. \<lbrakk>l < #:c\<^isub>1; Rep_wf_prog wfp = (c\<^isub>1, procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and> 
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))`
    note IH2 = `\<And>l wfp. \<lbrakk>l < #:c\<^isub>2; Rep_wf_prog wfp = (c\<^isub>2, procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and> 
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))`
    note [simp] = `Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)`
    show ?case
    proof(cases "l < #:c\<^isub>1")
      case True
      from `Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)`
      obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c\<^isub>1, procs)" by(erule wfp_Seq1)
      from IH1[OF True this] obtain as as' 
	where path1:"wfp' \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit)"
	and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
	and path2:"wfp' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l)"
	and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
      from path1 have "as \<noteq> []" by(fastsimp elim:ProcCFG.path.cases)
      then obtain ax asx where [simp]:"as = asx@[ax]"
	by(cases as rule:rev_cases) fastsimp+
      with path1 have "wfp' \<turnstile> (Main, Label l) -asx\<rightarrow>* sourcenode ax"
	and "valid_edge wfp' ax" and "targetnode ax = (Main, Exit)"
	by(auto elim:ProcCFG.path_split_snoc)
      from `valid_edge wfp' ax` `targetnode ax = (Main, Exit)`
      obtain nx where "sourcenode ax = (Main,nx)" 
	by(fastsimp elim:PCFG.cases simp:valid_edge_def)
      with `wfp' \<turnstile> (Main, Label l) -asx\<rightarrow>* sourcenode ax` have "nx \<noteq> Entry"
	by fastsimp
      moreover
      from `valid_edge wfp' ax` `sourcenode ax = (Main,nx)` have "nx \<noteq> Exit"
	by(fastsimp intro:ProcCFGExit.Exit_source)
      ultimately obtain lx where [simp]:"nx = Label lx" by(cases nx) auto
      with `wfp' \<turnstile> (Main, Label l) -asx\<rightarrow>* sourcenode ax` 
	`sourcenode ax = (Main,nx)` intra1
      have path3:"wfp \<turnstile> (Main, Label l) -asx\<rightarrow>* (Main, Label lx)"
	by -(rule path_SeqFirst,auto)
      from `valid_edge wfp' ax` `targetnode ax = (Main, Exit)`
	`sourcenode ax = (Main,nx)` wf
      obtain etx where "c\<^isub>1 \<turnstile> Label lx -etx\<rightarrow>\<^isub>p Exit" 
	by(fastsimp elim!:PCFG.cases simp:valid_edge_def)
      then obtain et where [simp]:"etx = IEdge et" 
	by(cases etx)(auto dest:Proc_CFG_Call_Labels)
      with `c\<^isub>1 \<turnstile> Label lx -etx\<rightarrow>\<^isub>p Exit` have "intra_kind et"
	by(fastsimp intro:Proc_CFG_IEdge_intra_kind)
      from `c\<^isub>1 \<turnstile> Label lx -etx\<rightarrow>\<^isub>p Exit` path3
      have path4:"wfp \<turnstile> (Main, Label l) -asx@
	[((Main, Label lx),et,(Main,Label 0 \<oplus> #:c\<^isub>1))] \<rightarrow>* (Main,Label 0 \<oplus> #:c\<^isub>1)"
	by(fastsimp intro:ProcCFG.path_Append ProcCFG.path.intros Proc_CFG_SeqConnect
	  Main simp:ProcCFG.valid_node_def valid_edge_def)
      from `Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)`
      obtain wfp'' where [simp]:"Rep_wf_prog wfp'' = (c\<^isub>2, procs)" by(erule wfp_Seq2)
      from IH2[OF _ this,of "0"] obtain asx' 
	where "wfp'' \<turnstile> (Main, Label 0) -asx'\<rightarrow>* (Main, Exit)"
	and "\<forall>a\<in>set asx'. intra_kind (kind a)" by blast
      with path4 intra1 `intra_kind et` have "wfp \<turnstile> (Main, Label l) 
	-(asx@[((Main, Label lx),et,(Main,Label 0 \<oplus> #:c\<^isub>1))])@(asx' \<oplus>s #:c\<^isub>1)\<rightarrow>*
	(Main, Exit \<oplus> #:c\<^isub>1)"
	by -(erule ProcCFG.path_Append,rule path_Main_SeqSecond,auto)
      moreover
      from intra1 `intra_kind et` `\<forall>a\<in>set asx'. intra_kind (kind a)`
      have "\<forall>a \<in> set ((asx@[((Main, Label lx),et,(Main,Label #:c\<^isub>1))])@(asx' \<oplus>s #:c\<^isub>1)).
	intra_kind (kind a)" by(auto simp:label_incrs_def)
      moreover
      from path2 intra2 have "wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l)"
	by -(rule path_SeqFirst,auto)
      ultimately show ?thesis using `\<forall>a\<in>set as'. intra_kind (kind a)` by fastsimp
    next
      case False
      hence "#:c\<^isub>1 \<le> l" by simp
      then obtain l' where [simp]:"l = l' + #:c\<^isub>1" and "l' = l - #:c\<^isub>1" by simp
      from `l < #:c\<^isub>1;; c\<^isub>2` have "l' < #:c\<^isub>2" by simp
      from `Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)`
      obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c\<^isub>2, procs)" by(erule wfp_Seq2)
      from IH2[OF `l' < #:c\<^isub>2` this] obtain as as' 
	where path1:"wfp' \<turnstile> (Main, Label l') -as\<rightarrow>* (Main, Exit)"
	and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
	and path2:"wfp' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l')"
	and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
      from path1 intra1
      have "wfp \<turnstile> (Main, Label l' \<oplus> #:c\<^isub>1) -as \<oplus>s #:c\<^isub>1\<rightarrow>* (Main, Exit \<oplus> #:c\<^isub>1)"
	by -(rule path_Main_SeqSecond,auto)
      moreover
      from path2 have "as' \<noteq> []" by(fastsimp elim:ProcCFG.path.cases)
      with path2 obtain ax' asx' where [simp]:"as' = ax'#asx'"
	and "sourcenode ax' = (Main, Entry)" and "valid_edge wfp' ax'" 
	and "wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')"
	by -(erule ProcCFG.path_split_Cons,fastsimp+)
      from `wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')`
      have "targetnode ax' \<noteq> (Main,Exit)" by fastsimp
      with `valid_edge wfp' ax'` `sourcenode ax' = (Main, Entry)` wf
      have "targetnode ax' = (Main,Label 0)"
	by(fastsimp elim:PCFG.cases dest:Proc_CFG_EntryD simp:valid_edge_def)
      with `wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')` intra2
      have path3:"wfp \<turnstile> (Main,Label 0 \<oplus> #:c\<^isub>1) -asx' \<oplus>s #:c\<^isub>1\<rightarrow>* 
	(Main, Label l' \<oplus> #:c\<^isub>1)" by -(rule path_Main_SeqSecond,auto)
      from `Rep_wf_prog wfp = (c\<^isub>1;; c\<^isub>2, procs)`
      obtain wfp'' where [simp]:"Rep_wf_prog wfp'' = (c\<^isub>1, procs)" by(erule wfp_Seq1)
      from IH1[OF _ this,of "0"] obtain xs 
	where "wfp'' \<turnstile> (Main, Label 0) -xs\<rightarrow>* (Main, Exit)"
	and "\<forall>a\<in>set xs. intra_kind (kind a)" by blast
      from `wfp'' \<turnstile> (Main, Label 0) -xs\<rightarrow>* (Main, Exit)` have "xs \<noteq> []"
	by(fastsimp elim:ProcCFG.path.cases)
      then obtain x xs' where [simp]:"xs = xs'@[x]"
	by(cases xs rule:rev_cases) fastsimp+
      with `wfp'' \<turnstile> (Main, Label 0) -xs\<rightarrow>* (Main, Exit)`
      have "wfp'' \<turnstile> (Main, Label 0) -xs'\<rightarrow>* sourcenode x"
	and "valid_edge wfp'' x" and "targetnode x = (Main, Exit)"
	by(auto elim:ProcCFG.path_split_snoc)
      from `valid_edge wfp'' x` `targetnode x = (Main, Exit)`
      obtain nx where "sourcenode x = (Main,nx)" 
	by(fastsimp elim:PCFG.cases simp:valid_edge_def)
      with `wfp'' \<turnstile> (Main, Label 0) -xs'\<rightarrow>* sourcenode x` have "nx \<noteq> Entry"
	by fastsimp
      from `valid_edge wfp'' x` `sourcenode x = (Main,nx)` have "nx \<noteq> Exit"
	by(fastsimp intro:ProcCFGExit.Exit_source)
      with `nx \<noteq> Entry` obtain lx where [simp]:"nx = Label lx" by(cases nx) auto
      from `wfp'' \<turnstile> (Main, Label 0) -xs'\<rightarrow>* sourcenode x` 
	`sourcenode x = (Main,nx)` `\<forall>a\<in>set xs. intra_kind (kind a)`
      have "wfp \<turnstile> (Main, Entry) 
	-((Main, Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main, Label 0))#xs'\<rightarrow>* sourcenode x"
	apply simp apply(rule path_SeqFirst[OF `Rep_wf_prog wfp'' = (c\<^isub>1, procs)`])
	apply(auto intro!:ProcCFG.Cons_path)
	by(auto intro:Main Proc_CFG_Entry simp:valid_edge_def intra_kind_def)
      with `valid_edge wfp'' x` `targetnode x = (Main, Exit)` path3
	`sourcenode x = (Main,nx)` `nx \<noteq> Entry` `sourcenode x = (Main,nx)` wf
      have "wfp \<turnstile> (Main, Entry) -((((Main, Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main, Label 0))#xs')@
	[(sourcenode x,kind x,(Main,Label #:c\<^isub>1))])@(asx' \<oplus>s #:c\<^isub>1)\<rightarrow>* 
	(Main, Label l' \<oplus> #:c\<^isub>1)" 
	by(fastsimp intro:ProcCFG.path_Append ProcCFG.path.intros Main 
	  Proc_CFG_SeqConnect elim!:PCFG.cases dest:Proc_CFG_Call_Labels
	  simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis using intra1 intra2 `\<forall>a\<in>set xs. intra_kind (kind a)`
	by(fastsimp simp:label_incrs_def intra_kind_def)
    qed
  next
    case (Cond b c\<^isub>1 c\<^isub>2)
    note IH1 = `\<And>l wfp. \<lbrakk>l < #:c\<^isub>1; Rep_wf_prog wfp = (c\<^isub>1, procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and> 
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))`
    note IH2 = `\<And>l wfp. \<lbrakk>l < #:c\<^isub>2; Rep_wf_prog wfp = (c\<^isub>2, procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and> 
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))`
    note [simp] = `Rep_wf_prog wfp = (if (b) c\<^isub>1 else c\<^isub>2, procs)`
    show ?case
    proof(cases "l = 0")
      case True
      from `Rep_wf_prog wfp = (if (b) c\<^isub>1 else c\<^isub>2, procs)`
      obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c\<^isub>1, procs)" by(erule wfp_CondTrue)
      from IH1[OF _ this,of 0] obtain as 
	where path:"wfp' \<turnstile> (Main, Label 0) -as\<rightarrow>* (Main, Exit)"
	and intra:"\<forall>a\<in>set as. intra_kind (kind a)" by blast
      have "if (b) c\<^isub>1 else c\<^isub>2,procs \<turnstile> (Main,Label 0)
	-(\<lambda>cf. state_check cf b (Some true))\<^isub>\<surd>\<rightarrow> (Main,Label 0 \<oplus> 1)"
	by(fastsimp intro:Main Proc_CFG_CondTrue)
      with path intra have "wfp \<turnstile> (Main,Label 0)
	-[((Main,Label 0),(\<lambda>cf. state_check cf b (Some true))\<^isub>\<surd>,(Main,Label 0 \<oplus> 1))]@
	(as \<oplus>s 1)\<rightarrow>* (Main,Exit \<oplus> 1)"
	apply - apply(rule ProcCFG.path_Append)	apply(rule ProcCFG.path.intros)+
	prefer 5 apply(rule path_Main_CondTrue)
	apply(auto intro:ProcCFG.path.intros simp:valid_edge_def)
	by(fastsimp simp:ProcCFG.valid_node_def valid_edge_def)
      moreover
      have "if (b) c\<^isub>1 else c\<^isub>2,procs \<turnstile> (Main,Entry) -(\<lambda>s. True)\<^isub>\<surd>\<rightarrow> 
	(Main,Label 0)" by(fastsimp intro:Main Proc_CFG_Entry)
      hence "wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))]\<rightarrow>* 
	(Main,Label 0)"
	by(fastsimp intro:ProcCFG.path.intros 
	            simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis using `l = 0` `\<forall>a\<in>set as. intra_kind (kind a)` 
	by(fastsimp simp:label_incrs_def intra_kind_def)
    next
      case False
      hence "0 < l" by simp
      then obtain l' where [simp]:"l = l' + 1" and "l' = l - 1" by simp
      show ?thesis
      proof(cases "l' < #:c\<^isub>1")
	case True
	from `Rep_wf_prog wfp = (if (b) c\<^isub>1 else c\<^isub>2, procs)`
	obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c\<^isub>1, procs)" 
	  by(erule wfp_CondTrue)
	from IH1[OF True this] obtain as as' 
	  where path1:"wfp' \<turnstile> (Main, Label l') -as\<rightarrow>* (Main, Exit)"
	  and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
	  and path2:"wfp' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l')"
	  and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
	from path1 intra1
	have "wfp \<turnstile> (Main, Label l' \<oplus> 1) -as \<oplus>s 1\<rightarrow>* (Main, Exit \<oplus> 1)"
	  by -(rule path_Main_CondTrue,auto)
	moreover
	from path2 obtain ax' asx' where [simp]:"as' = ax'#asx'"
	  and "sourcenode ax' = (Main,Entry)" and "valid_edge wfp' ax'"
	  and "wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')"
	  by -(erule ProcCFG.path.cases,fastsimp+)
	with wf have "targetnode ax' = (Main,Label 0)"
	  by(fastsimp elim:PCFG.cases dest:Proc_CFG_EntryD Proc_CFG_Call_Labels 
	              simp:valid_edge_def)
	with `wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')` intra2
	have "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))#
	  ((Main,Label 0),(\<lambda>cf. state_check cf b (Some true))\<^isub>\<surd>,(Main,Label 0 \<oplus> 1))#
	  (asx' \<oplus>s 1)\<rightarrow>* (Main,Label l' \<oplus> 1)"
	  apply - apply(rule ProcCFG.path.intros)+ apply(rule path_Main_CondTrue) 
	  by(auto intro:Main Proc_CFG_Entry Proc_CFG_CondTrue simp:valid_edge_def)
	ultimately show ?thesis using intra1 intra2
	  by(fastsimp simp:label_incrs_def intra_kind_def)
      next
	case False
	hence "#:c\<^isub>1 \<le> l'" by simp
	then obtain l'' where [simp]:"l' = l'' + #:c\<^isub>1" and "l'' = l' - #:c\<^isub>1" by simp
	from  `l < #:(if (b) c\<^isub>1 else c\<^isub>2)` have "l'' < #:c\<^isub>2" by simp
	from `Rep_wf_prog wfp = (if (b) c\<^isub>1 else c\<^isub>2, procs)`
	obtain wfp'' where [simp]:"Rep_wf_prog wfp'' = (c\<^isub>2, procs)" 
	  by(erule wfp_CondFalse)
	from IH2[OF `l'' < #:c\<^isub>2` this] obtain as as' 
	  where path1:"wfp'' \<turnstile> (Main, Label l'') -as\<rightarrow>* (Main, Exit)"
	  and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
	  and path2:"wfp'' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l'')"
	  and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
	from path1 intra1
	have "wfp \<turnstile> (Main, Label l'' \<oplus> (#:c\<^isub>1 + 1)) -as \<oplus>s (#:c\<^isub>1 + 1)\<rightarrow>* 
	  (Main, Exit \<oplus> (#:c\<^isub>1 + 1))"
	  by -(rule path_Main_CondFalse,auto simp:add_assoc)
	moreover
	from path2 obtain ax' asx' where [simp]:"as' = ax'#asx'"
	  and "sourcenode ax' = (Main,Entry)" and "valid_edge wfp'' ax'"
	  and "wfp'' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l'')"
	  by -(erule ProcCFG.path.cases,fastsimp+)
	with wf have "targetnode ax' = (Main,Label 0)"
	  by(fastsimp elim:PCFG.cases dest:Proc_CFG_EntryD Proc_CFG_Call_Labels 
	              simp:valid_edge_def)
	with `wfp'' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l'')` intra2
	have "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))#
	  ((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^isub>\<surd>,
	  (Main,Label (#:c\<^isub>1 + 1)))#(asx' \<oplus>s (#:c\<^isub>1 + 1))\<rightarrow>* 
	  (Main,Label l'' \<oplus> (#:c\<^isub>1 + 1))"
	  apply - apply(rule ProcCFG.path.intros)+ apply(rule path_Main_CondFalse)
	  by(auto intro:Main Proc_CFG_Entry Proc_CFG_CondFalse simp:valid_edge_def)
	ultimately show ?thesis using intra1 intra2
	  by(fastsimp simp:label_incrs_def intra_kind_def add_assoc)
      qed
    qed
  next
    case (While b c')
    note IH = `\<And>l wfp. \<lbrakk>l < #:c'; Rep_wf_prog wfp = (c', procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and>
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))`
    note [simp] = `Rep_wf_prog wfp = (while (b) c', procs)`
    show ?case
    proof(cases "l = 0")
      case True
      hence "wfp \<turnstile> (Main,Label l) - 
	((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^isub>\<surd>,(Main,Label 1))#
	[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
	by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_WhileFalseSkip 
	  Proc_CFG_WhileFalse simp:valid_edge_def)
      moreover
      have "while (b) c' \<turnstile> Entry -IEdge (\<lambda>s. True)\<^isub>\<surd>\<rightarrow>\<^isub>p Label 0" by(rule Proc_CFG_Entry)
      with `l = 0` have "wfp \<turnstile> (Main,Entry) 
	-[((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))]\<rightarrow>* (Main,Label l)"
	by(fastsimp intro:ProcCFG.path.intros Main 
	             simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis by(fastsimp simp:intra_kind_def)
    next
      case False
      hence "1 \<le> l" by simp
      thus ?thesis
      proof(cases "l < 2")
	case True
	with `1 \<le> l` have [simp]:"l = 1" by simp
	have "wfp \<turnstile> (Main,Label l) -[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
	  by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_WhileFalseSkip 
	              simp:valid_edge_def)
	moreover
	have "while (b) c' \<turnstile> Label 0 -IEdge (\<lambda>cf. state_check cf b (Some false))\<^isub>\<surd>\<rightarrow>\<^isub>p 
	  Label 1" by(rule Proc_CFG_WhileFalse)
	hence "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))#
	  [((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^isub>\<surd>,(Main,Label 1))]\<rightarrow>*
	  (Main,Label l)"
	  by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_Entry 
	               simp:ProcCFG.valid_node_def valid_edge_def)
	ultimately show ?thesis by(fastsimp simp:intra_kind_def)
      next
	case False
	with `1 \<le> l` have "2 \<le> l" by simp
	then obtain l' where [simp]:"l = l' + 2" and "l' = l - 2" 
	  by(simp del:add_2_eq_Suc')
	from `l < #:while (b) c'` have "l' < #:c'" by simp
	from `Rep_wf_prog wfp = (while (b) c', procs)`
	obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c', procs)" 
	  by(erule wfp_WhileBody)
	from IH[OF `l' < #:c'` this] obtain as as' 
	  where path1:"wfp' \<turnstile> (Main, Label l') -as\<rightarrow>* (Main, Exit)"
	  and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
	  and path2:"wfp' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l')"
	  and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
	from path1 have "as \<noteq> []" by(fastsimp elim:ProcCFG.path.cases)
	with path1 obtain ax asx where [simp]:"as = asx@[ax]"
	  and "wfp' \<turnstile> (Main, Label l') -asx\<rightarrow>* sourcenode ax"
	  and "valid_edge wfp' ax" and "targetnode ax = (Main, Exit)"
	  by -(erule ProcCFG.path_split_snoc,fastsimp+)
	with wf obtain lx etx where "sourcenode ax = (Main,Label lx)"
	  and "intra_kind (kind ax)"
	  apply(auto elim!:PCFG.cases dest:Proc_CFG_Call_Labels simp:valid_edge_def)
	  by(case_tac n)(auto dest:Proc_CFG_IEdge_intra_kind)
	with `wfp' \<turnstile> (Main, Label l') -asx\<rightarrow>* sourcenode ax` intra1
	have "wfp \<turnstile> (Main, Label l' \<oplus> 2) -asx \<oplus>s 2\<rightarrow>* (Main,Label lx \<oplus> 2)"
	  by -(rule path_Main_WhileBody,auto)
	from `valid_edge wfp' ax` `sourcenode ax = (Main,Label lx)`
	  `targetnode ax = (Main, Exit)` `intra_kind (kind ax)` wf
	have "while (b) c',procs \<turnstile> (Main,Label lx \<oplus> 2) -kind ax\<rightarrow> 
	  (Main,Label 0)"
	  by(fastsimp intro!:Main Proc_CFG_WhileBodyExit elim!:PCFG.cases 
	                dest:Proc_CFG_Call_Labels simp:valid_edge_def)
	hence "wfp \<turnstile> (Main,Label lx \<oplus> 2) 
	  -((Main,Label lx \<oplus> 2),kind ax,(Main,Label 0))#
	  ((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^isub>\<surd>,(Main,Label 1))#
	  [((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
	  by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_WhileFalse 
	    Proc_CFG_WhileFalseSkip simp:valid_edge_def)
	with `wfp \<turnstile> (Main, Label l' \<oplus> 2) -asx \<oplus>s 2\<rightarrow>* (Main,Label lx \<oplus> 2)`
	have "wfp \<turnstile> (Main, Label l) -(asx \<oplus>s 2)@
	  (((Main,Label lx \<oplus> 2),kind ax,(Main,Label 0))#
	  ((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^isub>\<surd>,(Main,Label 1))#
	  [((Main,Label 1),\<Up>id,(Main,Exit))])\<rightarrow>* (Main,Exit)"
	  by(fastsimp intro:ProcCFG.path_Append)
	moreover
	from path2 have "as' \<noteq> []" by(fastsimp elim:ProcCFG.path.cases)
	with path2 obtain ax' asx' where [simp]:"as' = ax'#asx'"
	  and "wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main,Label l')"
	  and "valid_edge wfp' ax'" and "sourcenode ax' = (Main, Entry)"
	  by -(erule ProcCFG.path_split_Cons,fastsimp+)
	with wf have "targetnode ax' = (Main,Label 0)" and "intra_kind (kind ax')"
	  by(fastsimp elim!:PCFG.cases dest:Proc_CFG_Call_Labels 
	    Proc_CFG_EntryD simp:intra_kind_def valid_edge_def)+
	with `wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main,Label l')` intra2
	have "wfp \<turnstile> (Main, Label 0 \<oplus> 2) -asx' \<oplus>s 2\<rightarrow>* (Main,Label l' \<oplus> 2)"
	  by -(rule path_Main_WhileBody,auto simp del:add_2_eq_Suc')
	hence "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))#
	  ((Main,Label 0),(\<lambda>cf. state_check cf b (Some true))\<^isub>\<surd>,(Main,Label 2))#
	  (asx' \<oplus>s 2)\<rightarrow>* (Main,Label l)"
	  by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_WhileTrue 
	    Proc_CFG_Entry simp:valid_edge_def)
	ultimately show ?thesis using `intra_kind (kind ax)` intra1 intra2
	  by(fastsimp simp:label_incrs_def intra_kind_def)
      qed
    qed
  next
    case (Call p es rets)
    note Rep [simp] = `Rep_wf_prog wfp = (Call p es rets, procs)`
    have cC:"containsCall procs (Call p es rets) [] p es rets" by simp
    have "distinct rets"
      by(fastsimp intro:wf_distinct_rets[OF _ cC] wf_wf_prog[OF Rep])
    show ?case
    proof(cases "l = 0")
      case True
      from `distinct rets` 
      have "wfp \<turnstile> (Main,Label 0) -((Main,Label 0),(\<lambda>s. False)\<^isub>\<surd>,(Main,Label 1))#
	[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
	by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_CallSkip MainCallReturn
	  Proc_CFG_Call simp:valid_edge_def)
      moreover
      have "Call p es rets,procs \<turnstile> (Main,Entry) -(\<lambda>s. True)\<^isub>\<surd>\<rightarrow> (Main,Label 0)"
	by(fastsimp intro:Main Proc_CFG_Entry)
      hence "wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))]\<rightarrow>*
	(Main,Label 0)"
	by(fastsimp intro:ProcCFG.path.intros 
	  simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis using `l = 0` by(fastsimp simp:intra_kind_def)
    next
      case False
      with `l < #:Call p es rets` have "l = 1" by simp
      have "wfp \<turnstile> (Main,Label 1) -[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
	by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_CallSkip
	            simp:valid_edge_def)
      moreover
      from `distinct rets` 
      have "Call p es rets,procs \<turnstile> (Main,Label 0) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,Label 1)"
	by(fastsimp intro:MainCallReturn Proc_CFG_Call)
      hence "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^isub>\<surd>,(Main,Label 0))#
	[((Main,Label 0),(\<lambda>s. False)\<^isub>\<surd>,(Main,Label 1))]\<rightarrow>* (Main,Label 1)"
	by(fastsimp intro:ProcCFG.path.intros Main Proc_CFG_Entry 
	            simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis using `l = 1` by(fastsimp simp:intra_kind_def)
    qed
  qed
qed


subsection {* Lifting from edges in procedure Main to arbitrary procedures *}

lemma lift_edge_Main_Main:
  "\<lbrakk>c,procs \<turnstile> (Main, n) -et\<rightarrow> (Main, n'); (p,ins,outs,c) \<in> set procs;
  containsCall procs prog ps p es rets; well_formed procs\<rbrakk> 
  \<Longrightarrow> prog,procs \<turnstile> (p, n) -et\<rightarrow> (p, n')"
proof(induct x\<equiv>"(Main,n)" et x'\<equiv>"(Main,n')" rule:PCFG.induct)
  case Main thus ?case by(fastsimp intro:Proc)
next
  case MainCallReturn thus ?case by(fastsimp intro:ProcCallReturn)
qed auto

lemma lift_edge_Main_Proc:
  "\<lbrakk>c,procs \<turnstile> (Main, n) -et\<rightarrow> (q, n'); q \<noteq> Main; (p,ins,outs,c) \<in> set procs;
  containsCall procs prog ps p es rets; well_formed procs\<rbrakk> 
  \<Longrightarrow> \<exists>et'. prog,procs \<turnstile> (p, n) -et'\<rightarrow> (q, n')"
proof(induct x\<equiv>"(Main,n)" et x'\<equiv>"(q,n')" rule:PCFG.induct)
  case (MainCall l px esx retsx n'x insx outsx cx)
  from `c \<turnstile> Label l -CEdge (px, esx, retsx)\<rightarrow>\<^isub>p n'x` 
  obtain l' where [simp]:"n'x = Label l'" by(fastsimp dest:Proc_CFG_Call_Labels)
  from `(Main, Label l) = (Main, n)` `(px, Entry) = (q, n')`
  have [simp]:"n = Label l" "n' = Entry" "px = q" by simp_all
  from `(p, ins, outs, c) \<in> set procs` obtain i where "i < length procs"
    and "procs!i = (p, ins, outs, c)" by(auto simp:set_conv_nth)
  with MainCall(1-9) have "prog,procs \<turnstile> (p, Label l) 
    -(\<lambda>s. True)\<hookrightarrow>\<^bsub>q\<^esub>set_params (Suc i) (Suc l) esx\<rightarrow> (q, Entry)"
    by(fastsimp intro!:ProcCall)
  thus ?case by fastsimp
qed auto

lemma lift_edge_Proc_Main:
  "\<lbrakk>c,procs \<turnstile> (q, n) -et\<rightarrow> (Main, n'); q \<noteq> Main; (p,ins,outs,c) \<in> set procs;
  containsCall procs prog ps p es rets; well_formed procs\<rbrakk> 
  \<Longrightarrow> \<exists>et'. prog,procs \<turnstile> (q, n) -et'\<rightarrow> (p, n')"
proof(induct x\<equiv>"(q,n)" et x'\<equiv>"(Main,n')" rule:PCFG.induct)
  case (MainReturn l px esx retsx l' insx outsx cx)
  from `(px, Exit) = (q, n)` `(Main, Label l') = (Main, n')`
  have [simp]:"n = Exit" "n' = Label l'" "px = q" by simp_all
  from `(p, ins, outs, c) \<in> set procs` obtain i where "i < length procs"
    and "procs!i = (p, ins, outs, c)" by(auto simp:set_conv_nth)
  with MainReturn(1-9) have "prog,procs \<turnstile> (q,Exit) -(correct_return (Suc i) l')\<^bsub>q\<^esub>\<hookleftarrow>
    (\<lambda>cf cf'. cf'(map Loc retsx [:=] map cf outsx))\<rightarrow> (p,Label l')"
    by(fastsimp intro!:ProcReturn)
  thus ?case by fastsimp
qed auto


fun lift_edge :: "edge \<Rightarrow> pname \<Rightarrow> edge"
where "lift_edge a p = ((p,snd(sourcenode a)),kind a,(p,snd(targetnode a)))"

fun lift_path :: "edge list \<Rightarrow> pname \<Rightarrow> edge list"
  where "lift_path as p = map (\<lambda>a. lift_edge a p) as"


lemma lift_path_Proc: 
  assumes "Rep_wf_prog wfp' = (c,procs)" and "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "containsCall procs prog ps p es rets"
  shows "\<lbrakk>wfp' \<turnstile> (Main,n) -as\<rightarrow>* (Main,n'); \<forall>a \<in> set as. intra_kind (kind a)\<rbrakk>
  \<Longrightarrow> wfp \<turnstile> (p,n) -lift_path as p\<rightarrow>* (p,n')"
proof(induct x\<equiv>"(Main,n)" as x'\<equiv>"(Main,n')" arbitrary:n rule:ProcCFG.path.induct)
  case (empty_path m n)
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `m = (Main, n)` `m = (Main, n')` have [simp]:"n' = n" by simp
  from `CFG.valid_node sourcenode targetnode (valid_edge wfp') m` `m = (Main, n)`
    assms wf
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp) (p,n)"
    apply(auto simp:ProcCFG.valid_node_def valid_edge_def)
     apply(case_tac "ab = Main")
      apply(fastsimp dest:lift_edge_Main_Main)
     apply(fastsimp dest!:lift_edge_Main_Proc)
    apply(case_tac "a = Main")
     apply(fastsimp dest:lift_edge_Main_Main)
    by(fastsimp dest!:lift_edge_Proc_Main)
  thus ?case by(fastsimp dest:ProcCFG.empty_path)
next
  case (Cons_path m'' as m' a m n)
  note IH = `\<And>n. \<lbrakk>\<forall>a\<in>set as. intra_kind (kind a); m'' = (Main, n); m' = (Main, n')\<rbrakk>
    \<Longrightarrow> wfp \<turnstile> (p, n) -lift_path as p\<rightarrow>* (p, n')`
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs" 
    by(fastsimp intro:wf_wf_prog)
  from `\<forall>a\<in>set (a # as). intra_kind (kind a)` have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from `valid_edge wfp' a` `intra_kind (kind a)` `sourcenode a = m` 
    `targetnode a = m''` `m = (Main, n)` `Rep_wf_prog wfp' = (c,procs)`
  obtain n'' where "m'' = (Main, n'')"
    by(fastsimp elim:PCFG.cases simp:valid_edge_def intra_kind_def)
  with `valid_edge wfp' a` `Rep_wf_prog wfp' = (c,procs)`
    `sourcenode a = m` `targetnode a = m''` `m = (Main, n)`
    `(p,ins,outs,c) \<in> set procs` `containsCall procs prog ps p es rets` 
    `Rep_wf_prog wfp = (prog,procs)` wf
  have "prog,procs \<turnstile> (p, n) -kind a\<rightarrow> (p, n'')"
    by(auto intro:lift_edge_Main_Main simp:valid_edge_def)  
  from IH[OF `\<forall>a\<in>set as. intra_kind (kind a)` `m'' = (Main, n'')` `m' = (Main, n')`]
  have "wfp \<turnstile> (p, n'') -lift_path as p\<rightarrow>* (p, n')" .
  with `prog,procs \<turnstile> (p, n) -kind a\<rightarrow> (p, n'')` `Rep_wf_prog wfp = (prog,procs)`
    `sourcenode a = m` `targetnode a = m''` `m = (Main, n)` `m'' = (Main, n'')`
  show ?case by simp (rule ProcCFG.Cons_path,auto simp:valid_edge_def)
qed


subsection {* Existence of paths from Entry and to Exit *}

lemma Label_Proc_CFG_Entry_Exit_path_Proc:
  assumes "Rep_wf_prog wfp = (prog,procs)" and "l < #:c"
  and "(p,ins,outs,c) \<in> set procs" and "containsCall procs prog ps p es rets"
  obtains as as' where "wfp \<turnstile> (p,Label l) -as\<rightarrow>* (p,Exit)"
  and "\<forall>a \<in> set as. intra_kind (kind a)"
  and "wfp \<turnstile> (p,Entry) -as'\<rightarrow>* (p,Label l)"
  and "\<forall>a \<in> set as'. intra_kind (kind a)"
proof(atomize_elim)
  from `Rep_wf_prog wfp = (prog,procs)` `(p,ins,outs,c) \<in> set procs`
    `containsCall procs prog ps p es rets`
  obtain wfp' where "Rep_wf_prog wfp' = (c,procs)" by(erule wfp_Call)
  from this `l < #:c` obtain as as' where "wfp' \<turnstile> (Main,Label l) -as\<rightarrow>* (Main,Exit)"
    and "\<forall>a \<in> set as. intra_kind (kind a)"
    and "wfp' \<turnstile> (Main,Entry) -as'\<rightarrow>* (Main,Label l)"
    and "\<forall>a \<in> set as'. intra_kind (kind a)" 
    by(erule Label_Proc_CFG_Entry_Exit_path_Main)
  from `Rep_wf_prog wfp' = (c,procs)` `Rep_wf_prog wfp = (prog,procs)`
    `(p,ins,outs,c) \<in> set procs` `containsCall procs prog ps p es rets`
    `wfp' \<turnstile> (Main,Label l) -as\<rightarrow>* (Main,Exit)` `\<forall>a \<in> set as. intra_kind (kind a)`
  have "wfp \<turnstile> (p,Label l) -lift_path as p\<rightarrow>* (p,Exit)"
    by(fastsimp intro:lift_path_Proc)
  moreover
  from `Rep_wf_prog wfp' = (c,procs)` `Rep_wf_prog wfp = (prog,procs)`
    `(p,ins,outs,c) \<in> set procs` `containsCall procs prog ps p es rets`
    `wfp' \<turnstile> (Main,Entry) -as'\<rightarrow>* (Main,Label l)` `\<forall>a \<in> set as'. intra_kind (kind a)`
  have "wfp \<turnstile> (p,Entry) -lift_path as' p\<rightarrow>* (p,Label l)"
    by(fastsimp intro:lift_path_Proc)
  moreover
  from `\<forall>a \<in> set as. intra_kind (kind a)` `\<forall>a \<in> set as'. intra_kind (kind a)`
  have "\<forall>a \<in> set (lift_path as p). intra_kind (kind a)"
    and "\<forall>a \<in> set (lift_path as' p). intra_kind (kind a)" by auto
  ultimately
  show "\<exists>as as'. wfp \<turnstile> (p, Label l) -as\<rightarrow>* (p, Exit) \<and>
    (\<forall>a\<in>set as. intra_kind (kind a)) \<and> wfp \<turnstile> (p, Entry) -as'\<rightarrow>* (p, Label l) \<and>
    (\<forall>a\<in>set as'. intra_kind (kind a))" by fastsimp
qed


lemma Entry_to_Entry_and_Exit_to_Exit: 
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "containsCall procs prog ps p es rets" and "(p,ins,outs,c) \<in> set procs"
  obtains as as' where "CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (Main,Entry) as (p,Entry)"
  and "CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (p,Exit) as' (Main,Exit)"
proof(atomize_elim)
  from `containsCall procs prog ps p es rets` `(p,ins,outs,c) \<in> set procs`
  show "\<exists>as as'. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
    (get_return_edges wfp) (Main, Entry) as (p, Entry) \<and>
    CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
    (get_return_edges wfp) (p, Exit) as' (Main, Exit)"
  proof(induct ps arbitrary:p es rets ins outs c rule:rev_induct)
    case Nil
    from `containsCall procs prog [] p es rets`
    obtain lx lx' where "prog \<turnstile> Label lx -CEdge (p,es,rets)\<rightarrow>\<^isub>p Label lx'"
      by(erule containsCall_empty_Proc_CFG_Call_edge)
    moreover
    from `Rep_wf_prog wfp = (prog,procs)` `containsCall procs prog [] p es rets`
    have "distinct rets" by(fastsimp intro:wf_wf_prog)
    moreover
    from `Rep_wf_prog wfp = (prog,procs)` `containsCall procs prog [] p es rets`
      `(p, ins, outs, c) \<in> set procs`
    have "length rets = length outs" and "length es + 2 = length ins"
      by(auto intro:wf_length_retsI wf_length_esI wf_wf_prog simp del:add_2_eq_Suc')
    ultimately
    have "prog,procs \<turnstile> (Main,Label lx) -(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc lx) es\<rightarrow> 
      (p,Entry)" and "prog,procs \<turnstile> (p,Exit) -(correct_return 0 lx')\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs))\<rightarrow> (Main,Label lx')"
      using `(p, ins, outs, c) \<in> set procs`
      by -(rule MainCall,assumption+,rule MainReturn)
    with `Rep_wf_prog wfp = (prog,procs)`
    have "wfp \<turnstile> (Main,Label lx) -[((Main,Label lx),
      (\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc lx) es,(p,Entry))]\<rightarrow>* (p,Entry)"
      and "wfp \<turnstile> (p,Exit) -[((p,Exit),(correct_return 0 lx')\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs)),(Main,Label lx'))]\<rightarrow>* 
      (Main,Label lx')"
      by(fastsimp intro:ProcCFG.path.intros 
	simp:ProcCFG.valid_node_def valid_edge_def)+
    moreover
    from `prog \<turnstile> Label lx -CEdge (p,es,rets)\<rightarrow>\<^isub>p Label lx'`
    have "lx < #:prog" and "lx' < #:prog"
      by(auto intro:Proc_CFG_sourcelabel_less_num_nodes 
	            Proc_CFG_targetlabel_less_num_nodes)
    from `Rep_wf_prog wfp = (prog,procs)` `lx < #:prog` obtain as 
      where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label lx)"
      and "\<forall>a \<in> set as. intra_kind (kind a)"
      by -(erule Label_Proc_CFG_Entry_Exit_path_Main)
    moreover
    from `Rep_wf_prog wfp = (prog,procs)` `lx' < #:prog` obtain as' 
      where "wfp \<turnstile> (Main,Label lx') -as'\<rightarrow>* (Main,Exit)"
      and "\<forall>a \<in> set as'. intra_kind (kind a)"
      by -(erule Label_Proc_CFG_Entry_Exit_path_Main)
    moreover
    from `\<forall>a \<in> set as. intra_kind (kind a)` 
    have "CFG.valid_path kind (get_return_edges wfp) 
      (as@[((Main,Label lx),(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc lx) es,(p,Entry))])"
      by(fastsimp intro:ProcCFG.same_level_path_valid_path_Append 
	ProcCFG.intras_same_level_path simp:ProcCFG.valid_path_def)
    moreover
    from `\<forall>a \<in> set as'. intra_kind (kind a)` 
    have "CFG.valid_path kind (get_return_edges wfp) 
      ([((p,Exit),(correct_return 0 lx')\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs)),(Main,Label lx'))]@as')"
      by(fastsimp intro:ProcCFG.valid_path_same_level_path_Append 
	ProcCFG.intras_same_level_path simp:ProcCFG.valid_path_def)
    ultimately show ?case by(fastsimp intro:ProcCFG.path_Append simp:ProcCFG.vp_def)
  next
    case (snoc p' ps')
    note IH = `\<And>p es rets ins outs c. 
      \<lbrakk>containsCall procs prog ps' p es rets; (p,ins,outs,c) \<in> set procs\<rbrakk>
      \<Longrightarrow> \<exists>as as'. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (Main, Entry) as (p, Entry) \<and>
      CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (p, Exit) as' (Main, Exit)`
    from `containsCall procs prog (ps' @ [p']) p es rets`
    obtain ins' outs' c' es' rets' where "(p',ins',outs',c') \<in> set procs"
      and "containsCall procs c' [] p es rets" 
      and "containsCall procs prog ps' p' es' rets'" by(auto elim:containsCallE)
    from IH[OF `containsCall procs prog ps' p' es' rets'` 
      `(p',ins',outs',c') \<in> set procs`] 
    obtain as as' where pathE:"CFG.valid_path' sourcenode targetnode kind 
      (valid_edge wfp) (get_return_edges wfp) (Main, Entry) as (p', Entry)"
      and pathX:"CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (p', Exit) as' (Main, Exit)" by blast
    from `containsCall procs c' [] p es rets`
    obtain lx lx' where edge:"c' \<turnstile> Label lx -CEdge (p,es,rets)\<rightarrow>\<^isub>p Label lx'"
      by(erule containsCall_empty_Proc_CFG_Call_edge)
    hence "lx < #:c'" and "lx' < #:c'"
      by(auto intro:Proc_CFG_sourcelabel_less_num_nodes 
	            Proc_CFG_targetlabel_less_num_nodes)
    from `lx < #:c'` `Rep_wf_prog wfp = (prog,procs)` `(p',ins',outs',c') \<in> set procs`
      `containsCall procs prog ps' p' es' rets'` obtain asx 
      where "wfp \<turnstile> (p',Entry) -asx\<rightarrow>* (p',Label lx)"
      and "\<forall>a \<in> set asx. intra_kind (kind a)"
      by(fastsimp elim:Label_Proc_CFG_Entry_Exit_path_Proc)
    with pathE have pathE2:"CFG.valid_path' sourcenode targetnode kind 
      (valid_edge wfp) (get_return_edges wfp) (Main, Entry) (as@asx) (p', Label lx)"
      by(fastsimp intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
	ProcCFG.intras_same_level_path simp:ProcCFG.vp_def)
    from `lx' < #:c'` `Rep_wf_prog wfp = (prog,procs)`
      `(p',ins',outs',c') \<in> set procs` `containsCall procs prog ps' p' es' rets'` 
    obtain asx' where "wfp \<turnstile> (p',Label lx') -asx'\<rightarrow>* (p',Exit)"
      and "\<forall>a \<in> set asx'. intra_kind (kind a)"
      by(fastsimp elim:Label_Proc_CFG_Entry_Exit_path_Proc)
    with pathX have pathX2:"CFG.valid_path' sourcenode targetnode kind 
      (valid_edge wfp) (get_return_edges wfp) (p', Label lx') (asx'@as') (Main, Exit)"
      by(fastsimp intro:ProcCFG.path_Append ProcCFG.same_level_path_valid_path_Append
	ProcCFG.intras_same_level_path simp:ProcCFG.vp_def)
    from `(p',ins',outs',c') \<in> set procs` obtain i where "i < length procs" 
      and "procs!i = (p',ins',outs',c')" by(auto simp:set_conv_nth)
    moreover
    from `Rep_wf_prog wfp = (prog,procs)` `(p',ins',outs',c') \<in> set procs`
      `containsCall procs prog ps' p' es' rets'`
    obtain wfp' where "Rep_wf_prog wfp' = (c',procs)" by(erule wfp_Call)
    with `containsCall procs c' [] p es rets`
    have "distinct rets" by(fastsimp intro:wf_wf_prog)
    moreover
    from `Rep_wf_prog wfp' = (c',procs)` `containsCall procs c' [] p es rets`
      `(p,ins,outs,c) \<in> set procs`
    have "length rets = length outs" and "length es + 2 = length ins"
      by(auto intro:wf_length_retsI wf_length_esI wf_wf_prog simp del:add_2_eq_Suc')
    ultimately
    have "prog,procs \<turnstile> (p',Label lx) -(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params (Suc i) (Suc lx) es\<rightarrow> 
      (p,Entry)"
      and "prog,procs \<turnstile> (p,Exit) -(correct_return (Suc i) lx')\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs))\<rightarrow> (p',Label lx')"
      using edge `(p,ins,outs,c) \<in> set procs`
	`containsCall procs prog ps' p' es' rets'`
      by(fastsimp intro:ProcCall ProcReturn)+
    with `Rep_wf_prog wfp = (prog,procs)`
    have path:"wfp \<turnstile> (p',Label lx) -[((p',Label lx),
      (\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params (Suc i) (Suc lx) es,(p,Entry))]\<rightarrow>* (p,Entry)"
      and path':"wfp \<turnstile> (p,Exit) -[((p,Exit),(correct_return (Suc i) lx')\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs)),(p',Label lx'))]\<rightarrow>* 
      (p',Label lx')"
      by(fastsimp intro:ProcCFG.path.intros 
	          simp:ProcCFG.valid_node_def valid_edge_def)+
    from path pathE2 have "CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (Main, Entry) ((as@asx)@[((p',Label lx),
      (\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params (Suc i) (Suc lx) es,(p,Entry))]) (p,Entry)"
      apply(unfold ProcCFG.vp_def) apply(rule conjI)
       apply(fastsimp intro:ProcCFG.path_Append)
      by(unfold ProcCFG.valid_path_def,fastsimp intro:ProcCFG.vpa_snoc_Call)
    moreover
    from path' pathX2 have "CFG.valid_path' sourcenode targetnode kind 
      (valid_edge wfp) (get_return_edges wfp) (p,Exit)
      ([((p,Exit),(correct_return (Suc i) lx')\<^bsub>p\<^esub>\<hookleftarrow>
      (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs)),(p',Label lx'))]@(asx'@as'))
      (Main, Exit)"
      apply(unfold ProcCFG.vp_def) apply(rule conjI)
       apply(fastsimp intro:ProcCFG.path_Append)
      by(simp add:ProcCFG.valid_path_def ProcCFG.valid_path_def)
    ultimately show ?case by blast
  qed
qed


lemma edge_valid_paths:
  assumes "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
  and disj:"(p,n) = sourcenode a \<or> (p,n) = targetnode a" 
  and [simp]:"Rep_wf_prog wfp = (prog,procs)"
  shows "\<exists>as as'. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
                (get_return_edges wfp) (Main,Entry) as (p,n) \<and>
              CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
                (get_return_edges wfp) (p,n) as' (Main,Exit)"
proof -
  from `Rep_wf_prog wfp = (prog,procs)` have wf:"well_formed procs"
    by(fastsimp intro:wf_wf_prog)
  from `prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a`
  show ?thesis
  proof(induct x\<equiv>"sourcenode a" et\<equiv>"kind a" x'\<equiv>"targetnode a" rule:PCFG.induct)
    case (Main nx et nx')
    from disj Main(2)[THEN sym] Main(4)[THEN sym] have [simp]:"p = Main" by auto
    have "prog,procs \<turnstile> (Main, Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main, Exit)"
      by(fastsimp intro:PCFG.Main Proc_CFG_Entry_Exit)
    hence EXpath:"wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. False)\<^isub>\<surd>,(Main,Exit))]\<rightarrow>*
	(Main,Exit)"
      by(fastsimp intro:ProcCFG.path.intros
	simp:valid_edge_def ProcCFG.valid_node_def)
    show ?case
    proof(cases n)
      case (Label l)
      with `prog \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'` disj Main(2)[THEN sym] Main(4)[THEN sym]
      have "l < #:prog" by(auto intro:Proc_CFG_sourcelabel_less_num_nodes
	Proc_CFG_targetlabel_less_num_nodes)
      with `Rep_wf_prog wfp = (prog,procs)` 
      obtain as as' where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label l)"
	and "\<forall>a \<in> set as. intra_kind (kind a)"
	and "wfp \<turnstile> (Main,Label l) -as'\<rightarrow>* (Main,Exit)"
	and "\<forall>a \<in> set as'. intra_kind (kind a)"
	by -(erule Label_Proc_CFG_Entry_Exit_path_Main)+
      with Label show ?thesis
	apply(rule_tac x="as" in exI) apply(rule_tac x="as'" in exI) apply simp
	by(fastsimp intro:ProcCFG.intra_path_vp simp:ProcCFG.intra_path_def)
    next
      case Entry
      hence "wfp \<turnstile> (Main,Entry) -[]\<rightarrow>* (Main,n)" by(fastsimp intro:ProcCFG.empty_path)
      with EXpath show ?thesis by(fastsimp simp:ProcCFG.vp_def ProcCFG.valid_path_def)
    next
      case Exit
      hence "wfp \<turnstile> (Main,n) -[]\<rightarrow>* (Main,Exit)" by(fastsimp intro:ProcCFG.empty_path)
      with Exit EXpath show ?thesis using Exit
	apply(rule_tac x="[((Main,Entry),(\<lambda>s. False)\<^isub>\<surd>,(Main,Exit))]" in exI) 
	apply simp
	by(fastsimp intro:ProcCFG.intra_path_vp 
	  simp:ProcCFG.intra_path_def intra_kind_def)
    qed
  next
    case (Proc px ins outs c nx et nx' ps es rets)
    from `(px, ins, outs, c) \<in> set procs` wf have [simp]:"px \<noteq> Main" by auto
    from disj Proc(4)[THEN sym] Proc(6)[THEN sym] have [simp]:"p = px" by auto
    from `Rep_wf_prog wfp = (prog,procs)` 
      `containsCall procs prog ps px es rets` `(px, ins, outs, c) \<in> set procs`
    obtain asx asx' where path:"CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (Main,Entry) asx (px,Entry)"
      and path':"CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (px,Exit) asx' (Main,Exit)"
      by -(erule Entry_to_Entry_and_Exit_to_Exit)+
    from `containsCall procs prog ps px es rets` `(px, ins, outs, c) \<in> set procs`
    have "prog,procs \<turnstile> (px, Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (px, Exit)"
      by(fastsimp intro:PCFG.Proc Proc_CFG_Entry_Exit)
    hence EXpath:"wfp \<turnstile> (px,Entry) -[((px,Entry),(\<lambda>s. False)\<^isub>\<surd>,(px,Exit))]\<rightarrow>* 
      (px,Exit)" by(fastsimp intro:ProcCFG.path.intros 
	simp:valid_edge_def ProcCFG.valid_node_def)
    show ?case
    proof(cases n)
      case (Label l)
      with `c \<turnstile> nx -IEdge et\<rightarrow>\<^isub>p nx'` disj Proc(4)[THEN sym] Proc(6)[THEN sym]
      have "l < #:c" by(auto intro:Proc_CFG_sourcelabel_less_num_nodes
	Proc_CFG_targetlabel_less_num_nodes)
      with `Rep_wf_prog wfp = (prog,procs)` `(px, ins, outs, c) \<in> set procs` 
	`containsCall procs prog ps px es rets`
      obtain as as' where "wfp \<turnstile> (px,Entry) -as\<rightarrow>* (px,Label l)"
	and "\<forall>a \<in> set as. intra_kind (kind a)"
	and "wfp \<turnstile> (px,Label l) -as'\<rightarrow>* (px,Exit)"
	and "\<forall>a \<in> set as'. intra_kind (kind a)"
	by -(erule Label_Proc_CFG_Entry_Exit_path_Proc)+
      with path path' show ?thesis using Label
	apply(rule_tac x="asx@as" in exI) apply(rule_tac x="as'@asx'" in exI)
	by(auto intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
	  ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
	  simp:ProcCFG.vp_def)
    next
      case Entry
      from EXpath path' have "CFG.valid_path' sourcenode targetnode kind 
	(valid_edge wfp) (get_return_edges wfp) (px,Entry) 
	([((px,Entry),(\<lambda>s. False)\<^isub>\<surd>,(px,Exit))]@asx') (Main, Exit)"
	apply(unfold ProcCFG.vp_def) apply(erule conjE) apply(rule conjI)
	by(fastsimp intro:ProcCFG.path_Append 
	  ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
	  simp:intra_kind_def)+
      with path Entry show ?thesis by simp blast
    next
      case Exit
      with path EXpath path' show ?thesis
	apply(rule_tac x="asx@[((px,Entry),(\<lambda>s. False)\<^isub>\<surd>,(px,Exit))]" in exI)
	apply simp
	by(fastsimp intro:ProcCFG.path_Append 
	  ProcCFG.valid_path_same_level_path_Append ProcCFG.intras_same_level_path
	  simp:ProcCFG.vp_def ProcCFG.intra_path_def intra_kind_def)
    qed
  next
    case (MainCall l px es rets nx' ins outs c)
    from disj show ?case
    proof
      assume "(p,n) = sourcenode a"
      with MainCall(6)[THEN sym] have [simp]:"n = Label l" "p = Main" by simp_all
      with `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx'` have "l < #:prog"
	by(fastsimp intro:Proc_CFG_sourcelabel_less_num_nodes)
      with `Rep_wf_prog wfp = (prog,procs)` 
      obtain as as' where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label l)"
	and "\<forall>a \<in> set as. intra_kind (kind a)"
	and "wfp \<turnstile> (Main,Label l) -as'\<rightarrow>* (Main,Exit)"
	and "\<forall>a \<in> set as'. intra_kind (kind a)"
	by -(erule Label_Proc_CFG_Entry_Exit_path_Main)+
      thus ?thesis 
	by(fastsimp intro:ProcCFG.intra_path_vp simp:ProcCFG.intra_path_def)
    next
      assume "(p,n) = targetnode a"
      with MainCall(8)[THEN sym] have [simp]:"n = Entry" "p = px" by simp_all
      from `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx'`
      have "containsCall procs prog [] px es rets" 
	by(rule Proc_CFG_Call_containsCall)
      with `Rep_wf_prog wfp = (prog,procs)` `(px, ins, outs, c) \<in> set procs`
      obtain as' where Xpath:"CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (px,Exit) as' (Main,Exit)"
	by -(erule Entry_to_Entry_and_Exit_to_Exit)      
      from `containsCall procs prog [] px es rets` `(px, ins, outs, c) \<in> set procs`
      have "prog,procs \<turnstile> (px, Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (px, Exit)"
	by(fastsimp intro:PCFG.Proc Proc_CFG_Entry_Exit)
      hence "wfp \<turnstile> (px,Entry) -[((px,Entry),(\<lambda>s. False)\<^isub>\<surd>,(px,Exit))]\<rightarrow>* (px,Exit)"
	by(fastsimp intro:ProcCFG.path.intros 
	  simp:valid_edge_def ProcCFG.valid_node_def)
      with Xpath have "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (px,Entry) 
	([((px,Entry),(\<lambda>s. False)\<^isub>\<surd>,(px,Exit))]@as') (Main,Exit)"
	apply(unfold ProcCFG.vp_def) apply(erule conjE) apply(rule conjI)
	by(fastsimp intro:ProcCFG.path_Append 
	  ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
	  simp:intra_kind_def)+
      with `containsCall procs prog [] px es rets` `Rep_wf_prog wfp = (prog,procs)`
	`(px, ins, outs, c) \<in> set procs`
      show ?thesis by(fastsimp elim:Entry_to_Entry_and_Exit_to_Exit)
    qed
  next
    case (ProcCall i px ins outs c l p' es' rets' l' ins' outs' c' ps es rets)
    from `i < length procs` `procs ! i = (px, ins, outs, c)`[THEN sym]
    have "(px, ins, outs, c) \<in> set procs" by(auto simp:set_conv_nth)
    from disj show ?case
    proof
      assume "(p,n) = sourcenode a"
      with ProcCall(9)[THEN sym] have [simp]:"n = Label l" "p = px" by simp_all
      with `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'` have "l < #:c"
	by(fastsimp intro:Proc_CFG_sourcelabel_less_num_nodes)
      from `Rep_wf_prog wfp = (prog,procs)` `l < #:c` 
	`containsCall procs prog ps px es rets` `(px, ins, outs, c) \<in> set procs`
      obtain as as' where "wfp \<turnstile> (px,Label l) -as\<rightarrow>* (px,Exit)"
	and "\<forall>a \<in> set as. intra_kind (kind a)"
	and "wfp \<turnstile> (px,Entry) -as'\<rightarrow>* (px,Label l)"
	and "\<forall>a \<in> set as'. intra_kind (kind a)"
	by -(erule Label_Proc_CFG_Entry_Exit_path_Proc)+
      moreover
      from `Rep_wf_prog wfp = (prog,procs)` `containsCall procs prog ps px es rets`
	`(px, ins, outs, c) \<in> set procs` obtain asx asx' 
	where" CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (Main,Entry) asx (px,Entry)"
	and "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (px,Exit) asx' (Main,Exit)"
	by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis 
	apply(rule_tac x="asx@as'" in exI) apply(rule_tac x="as@asx'" in exI)
	by(auto intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
	  ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
	  simp:ProcCFG.vp_def)
    next
      assume "(p,n) = targetnode a"
      with ProcCall(11)[THEN sym] have [simp]:"n = Entry" "p = p'" by simp_all
      from `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
      have "containsCall procs c [] p' es' rets'" by(rule Proc_CFG_Call_containsCall)
      with `containsCall procs prog ps px es rets` `(px, ins, outs, c) \<in> set procs`
      have "containsCall procs prog (ps@[px]) p' es' rets'"
	by(rule containsCall_in_proc)
      with `(p', ins', outs', c') \<in> set procs`
      have "prog,procs \<turnstile> (p', Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (p', Exit)"
	by(fastsimp intro:PCFG.Proc Proc_CFG_Entry_Exit)
      hence "wfp \<turnstile> (p',Entry) -[((p',Entry),(\<lambda>s. False)\<^isub>\<surd>,(p',Exit))]\<rightarrow>* (p',Exit)"
	by(fastsimp intro:ProcCFG.path.intros 
	  simp:valid_edge_def ProcCFG.valid_node_def)
      moreover
      from `Rep_wf_prog wfp = (prog,procs)` `(p', ins', outs', c') \<in> set procs`
	`containsCall procs prog (ps@[px]) p' es' rets'`
      obtain as as' where "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (Main,Entry) as (p',Entry)"
	and "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (p',Exit) as' (Main,Exit)"
	by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis
	apply(rule_tac x="as" in exI)
	apply(rule_tac x="[((p',Entry),(\<lambda>s. False)\<^isub>\<surd>,(p',Exit))]@as'" in exI)
	apply(unfold ProcCFG.vp_def)
	by(fastsimp intro:ProcCFG.path_Append 
	  ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
	  simp:intra_kind_def)+
    qed
  next
    case (MainReturn l px es rets l' ins outs c)
    from disj show ?case
    proof
      assume "(p,n) = sourcenode a"
      with MainReturn(6)[THEN sym] have [simp]:"n = Exit" "p = px" by simp_all
      from `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^isub>p Label l'`
      have "containsCall procs prog [] px es rets" by(rule Proc_CFG_Call_containsCall)
      with `(px, ins, outs, c) \<in> set procs`
      have "prog,procs \<turnstile> (px, Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (px, Exit)"
	by(fastsimp intro:PCFG.Proc Proc_CFG_Entry_Exit)
      hence "wfp \<turnstile> (px,Entry) -[((px,Entry),(\<lambda>s. False)\<^isub>\<surd>,(px,Exit))]\<rightarrow>* (px,Exit)"
	by(fastsimp intro:ProcCFG.path.intros 
	  simp:valid_edge_def ProcCFG.valid_node_def)
      moreover
      from `Rep_wf_prog wfp = (prog,procs)` `(px, ins, outs, c) \<in> set procs`
	`containsCall procs prog [] px es rets`
      obtain as as' where "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (Main,Entry) as (px,Entry)"
	and "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (px,Exit) as' (Main,Exit)"
	by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis
	apply(rule_tac x="as@[((px,Entry),(\<lambda>s. False)\<^isub>\<surd>,(px,Exit))]" in exI)
	apply(rule_tac x="as'" in exI)
	apply(unfold ProcCFG.vp_def)
	by(fastsimp intro:ProcCFG.path_Append 
	  ProcCFG.valid_path_same_level_path_Append ProcCFG.intras_same_level_path
	  simp:intra_kind_def)+
    next
      assume "(p, n) = targetnode a"
      with MainReturn(8)[THEN sym] have [simp]:"n = Label l'" "p = Main" by simp_all
      with `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^isub>p Label l'` have "l' < #:prog"
	by(fastsimp intro:Proc_CFG_targetlabel_less_num_nodes)
      with `Rep_wf_prog wfp = (prog,procs)` 
      obtain as as' where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label l')"
	and "\<forall>a \<in> set as. intra_kind (kind a)"
	and "wfp \<turnstile> (Main,Label l') -as'\<rightarrow>* (Main,Exit)"
	and "\<forall>a \<in> set as'. intra_kind (kind a)"
	by -(erule Label_Proc_CFG_Entry_Exit_path_Main)+
      thus ?thesis 
	by(fastsimp intro:ProcCFG.intra_path_vp simp:ProcCFG.intra_path_def)
    qed
  next
    case (ProcReturn i px ins outs c l p' es' rets' l' ins' outs' c' ps es rets)
    from `i < length procs` `procs ! i = (px, ins, outs, c)`[THEN sym]
    have "(px, ins, outs, c) \<in> set procs" by(auto simp:set_conv_nth)
    from disj show ?case
    proof
      assume "(p,n) = sourcenode a"
      with ProcReturn(9)[THEN sym] have [simp]:"n = Exit" "p = p'" by simp_all
      from `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
      have "containsCall procs c [] p' es' rets'" by(rule Proc_CFG_Call_containsCall)
      with `containsCall procs prog ps px es rets` `(px, ins, outs, c) \<in> set procs`
      have "containsCall procs prog (ps@[px]) p' es' rets'"
	by(rule containsCall_in_proc)
      with `(p', ins', outs', c') \<in> set procs`
      have "prog,procs \<turnstile> (p', Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (p', Exit)"
	by(fastsimp intro:PCFG.Proc Proc_CFG_Entry_Exit)
      hence "wfp \<turnstile> (p',Entry) -[((p',Entry),(\<lambda>s. False)\<^isub>\<surd>,(p',Exit))]\<rightarrow>* (p',Exit)"
	by(fastsimp intro:ProcCFG.path.intros 
	  simp:valid_edge_def ProcCFG.valid_node_def)
      moreover
      from `Rep_wf_prog wfp = (prog,procs)` `(p', ins', outs', c') \<in> set procs`
	`containsCall procs prog (ps@[px]) p' es' rets'`
      obtain as as' where "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (Main,Entry) as (p',Entry)"
	and "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (p',Exit) as' (Main,Exit)"
	by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis
	apply(rule_tac x="as@[((p',Entry),(\<lambda>s. False)\<^isub>\<surd>,(p',Exit))]" in exI)
	apply(rule_tac x="as'" in exI)
	apply(unfold ProcCFG.vp_def)
	by(fastsimp intro:ProcCFG.path_Append 
	  ProcCFG.valid_path_same_level_path_Append ProcCFG.intras_same_level_path
	  simp:intra_kind_def)+
    next
      assume "(p, n) = targetnode a"
      with ProcReturn(11)[THEN sym] have [simp]:"n = Label l'" "p = px" by simp_all
      with `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'` have "l' < #:c"
	by(fastsimp intro:Proc_CFG_targetlabel_less_num_nodes)
      from `Rep_wf_prog wfp = (prog,procs)` `l' < #:c` 
	`containsCall procs prog ps px es rets` `(px, ins, outs, c) \<in> set procs`
      obtain as as' where "wfp \<turnstile> (px,Label l') -as\<rightarrow>* (px,Exit)"
	and "\<forall>a \<in> set as. intra_kind (kind a)"
	and "wfp \<turnstile> (px,Entry) -as'\<rightarrow>* (px,Label l')"
	and "\<forall>a \<in> set as'. intra_kind (kind a)"
	by -(erule Label_Proc_CFG_Entry_Exit_path_Proc)+
      moreover
      from `Rep_wf_prog wfp = (prog,procs)` `containsCall procs prog ps px es rets`
	`(px, ins, outs, c) \<in> set procs` obtain asx asx' 
	where" CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (Main,Entry) asx (px,Entry)"
	and "CFG.valid_path' sourcenode targetnode kind
	(valid_edge wfp) (get_return_edges wfp) (px,Exit) asx' (Main,Exit)"
	by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis 
	apply(rule_tac x="asx@as'" in exI) apply(rule_tac x="as@asx'" in exI)
	by(auto intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
	  ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
	  simp:ProcCFG.vp_def)
    qed
  next
    case (MainCallReturn nx px es rets nx')
    from `prog \<turnstile> nx -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx'` disj MainCallReturn(3)[THEN sym]
      MainCallReturn(5)[THEN sym] obtain l where [simp]:"n = Label l" "p = Main"
      by(fastsimp dest:Proc_CFG_Call_Labels)
    from `prog \<turnstile> nx -CEdge (px, es, rets)\<rightarrow>\<^isub>p nx'` disj MainCallReturn(3)[THEN sym]
      MainCallReturn(5)[THEN sym]
    have "l < #:prog" by(auto intro:Proc_CFG_sourcelabel_less_num_nodes
      Proc_CFG_targetlabel_less_num_nodes)
    with `Rep_wf_prog wfp = (prog,procs)` 
    obtain as as' where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label l)"
      and "\<forall>a \<in> set as. intra_kind (kind a)"
      and "wfp \<turnstile> (Main,Label l) -as'\<rightarrow>* (Main,Exit)"
      and "\<forall>a \<in> set as'. intra_kind (kind a)"
      by -(erule Label_Proc_CFG_Entry_Exit_path_Main)+
    thus ?thesis
      apply(rule_tac x="as" in exI) apply(rule_tac x="as'" in exI) apply simp
      by(fastsimp intro:ProcCFG.intra_path_vp simp:ProcCFG.intra_path_def)
  next
    case (ProcCallReturn px ins outs c nx p' es' rets' nx' ps es rets)
    from `(px, ins, outs, c) \<in> set procs` wf have [simp]:"px \<noteq> Main" by auto
    from `c \<turnstile> nx -CEdge (p', es', rets')\<rightarrow>\<^isub>p nx'` disj ProcCallReturn(5)[THEN sym]
      ProcCallReturn(7)[THEN sym] obtain l where [simp]:"n = Label l" "p = px"
      by(fastsimp dest:Proc_CFG_Call_Labels)
    from `c \<turnstile> nx -CEdge (p', es', rets')\<rightarrow>\<^isub>p nx'` disj ProcCallReturn(5)[THEN sym]
      ProcCallReturn(7)[THEN sym] have "l < #:c"
      by(auto intro:Proc_CFG_sourcelabel_less_num_nodes
	Proc_CFG_targetlabel_less_num_nodes)
    with `Rep_wf_prog wfp = (prog,procs)` `(px, ins, outs, c) \<in> set procs` 
      `containsCall procs prog ps px es rets`
    obtain as as' where "wfp \<turnstile> (px,Entry) -as\<rightarrow>* (px,Label l)"
      and "\<forall>a \<in> set as. intra_kind (kind a)"
      and "wfp \<turnstile> (px,Label l) -as'\<rightarrow>* (px,Exit)"
      and "\<forall>a \<in> set as'. intra_kind (kind a)"
      by -(erule Label_Proc_CFG_Entry_Exit_path_Proc)+
    moreover
    from `Rep_wf_prog wfp = (prog,procs)` 
      `containsCall procs prog ps px es rets` `(px, ins, outs, c) \<in> set procs`
    obtain asx asx' where "CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (Main,Entry) asx (px,Entry)"
      and "CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (px,Exit) asx' (Main,Exit)"
      by -(erule Entry_to_Entry_and_Exit_to_Exit)+
    ultimately show ?thesis
      apply(rule_tac x="asx@as" in exI) apply(rule_tac x="as'@asx'" in exI)
      by(auto intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
	ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
	simp:ProcCFG.vp_def)
  qed
qed



subsection {* Instantiating the @{text Postdomination} locale *}

interpretation ProcPostdomination:
  Postdomination sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main "(Main,Exit)"
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastsimp simp:wf_prog_def)
  hence wf:"well_formed procs" by(fastsimp intro:wf_wf_prog)
  show "Postdomination sourcenode targetnode kind (valid_edge wfp)
    (Main, Entry) get_proc (get_return_edges wfp) (lift_procs wfp) Main (Main, Exit)"
  proof
    fix m
    assume "CFG.valid_node sourcenode targetnode (valid_edge wfp) m"
    then obtain a where "valid_edge wfp a"
      and "m = sourcenode a \<or> m = targetnode a"
      by(fastsimp simp:ProcCFG.valid_node_def)
    obtain p n where [simp]:"m = (p,n)" by(cases m) auto
    from `valid_edge wfp a` `m = sourcenode a \<or> m = targetnode a` 
      `Rep_wf_prog wfp = (prog,procs)`
    show "\<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (Main, Entry) as m"
      by(auto dest!:edge_valid_paths simp:valid_edge_def)
  next
    fix m
    assume "CFG.valid_node sourcenode targetnode (valid_edge wfp) m"
    then obtain a where "valid_edge wfp a"
      and "m = sourcenode a \<or> m = targetnode a"
      by(fastsimp simp:ProcCFG.valid_node_def)
    obtain p n where [simp]:"m = (p,n)" by(cases m) auto
    from `valid_edge wfp a` `m = sourcenode a \<or> m = targetnode a` 
      `Rep_wf_prog wfp = (prog,procs)`
    show "\<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) m as (Main,Exit)"
      by(auto dest!:edge_valid_paths simp:valid_edge_def)
  next
    fix n n'
    assume mex1:"CFGExit.method_exit sourcenode kind (valid_edge wfp) (Main,Exit) n"
      and mex2:"CFGExit.method_exit sourcenode kind (valid_edge wfp) (Main,Exit) n'"
      and "get_proc n = get_proc n'"
    from mex1 
    have "n = (Main,Exit) \<or> (\<exists>a Q p f. n = sourcenode a \<and> valid_edge wfp a \<and> 
      kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f)" by(simp add:ProcCFGExit.method_exit_def)
    thus "n = n'"
    proof
      assume "n = (Main,Exit)"
      from mex2 have "n' = (Main,Exit) \<or> (\<exists>a Q p f. n' = sourcenode a \<and> 
	valid_edge wfp a \<and> kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f)" 
	by(simp add:ProcCFGExit.method_exit_def)
      thus ?thesis
      proof
	assume "n' = (Main,Exit)"
	with `n = (Main,Exit)` show ?thesis by simp
      next
	assume "\<exists>a Q p f. n' = sourcenode a \<and> 
	  valid_edge wfp a \<and> kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f"
	then obtain a Q p f where "n' = sourcenode a"
	  and "valid_edge wfp a" and "kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f" by blast
	from `valid_edge wfp a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	have "get_proc (sourcenode a) = p" by(rule ProcCFG.get_proc_return)
	with `get_proc n = get_proc n'` `n = (Main,Exit)` `n' = sourcenode a`
	have "get_proc (Main,Exit) = p" by simp
	hence "p = Main" by simp
	with `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f` have "kind a = Q\<^bsub>Main\<^esub>\<hookleftarrow>f" by simp
	with `valid_edge wfp a` have False by(rule ProcCFG.Main_no_return_source)
	thus ?thesis by simp
      qed
    next
      assume "\<exists>a Q p f. n = sourcenode a \<and> 
	valid_edge wfp a \<and> kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f"
      then obtain a Q p f where "n = sourcenode a"
	and "valid_edge wfp a" and "kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f" by blast
      from `valid_edge wfp a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
      have "get_proc (sourcenode a) = p" by(rule ProcCFG.get_proc_return)
      from mex2 have "n' = (Main,Exit) \<or> (\<exists>a Q p f. n' = sourcenode a \<and> 
	valid_edge wfp a \<and> kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f)" 
	by(simp add:ProcCFGExit.method_exit_def)
      thus ?thesis
      proof
	assume "n' = (Main,Exit)"
	from `get_proc (sourcenode a) = p` `get_proc n = get_proc n'`
	  `n' = (Main,Exit)` `n = sourcenode a`
	have "get_proc (Main,Exit) = p" by simp
	hence "p = Main" by simp
	with `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f` have "kind a = Q\<^bsub>Main\<^esub>\<hookleftarrow>f" by simp
	with `valid_edge wfp a` have False by(rule ProcCFG.Main_no_return_source)
	thus ?thesis by simp
      next
	assume "\<exists>a Q p f. n' = sourcenode a \<and> 
	  valid_edge wfp a \<and> kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f"
	then obtain a' Q' p' f' where "n' = sourcenode a'"
	  and "valid_edge wfp a'" and "kind a' = Q'\<^bsub>p'\<^esub>\<hookleftarrow>f'" by blast
	from `valid_edge wfp a'` `kind a' = Q'\<^bsub>p'\<^esub>\<hookleftarrow>f'`
	have "get_proc (sourcenode a') = p'" by(rule ProcCFG.get_proc_return)
	with `get_proc n = get_proc n'` `get_proc (sourcenode a) = p`
	  `n = sourcenode a` `n' = sourcenode a'`
	have "p' = p" by simp
	from `valid_edge wfp a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	have "sourcenode a = (p,Exit)" by(auto elim:PCFG.cases simp:valid_edge_def)
	from `valid_edge wfp a'` `kind a' = Q'\<^bsub>p'\<^esub>\<hookleftarrow>f'`
	have "sourcenode a' = (p',Exit)" by(auto elim:PCFG.cases simp:valid_edge_def)
	with `n = sourcenode a` `n' = sourcenode a'` `p' = p`
	  `sourcenode a = (p,Exit)` show ?thesis by simp
      qed
    qed
  qed
qed


end

