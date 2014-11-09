section {* Instantiate well-formedness locales with Proc CFG *}

theory WellFormed imports Interpretation Labels "../StaticInter/CFGExit_wf" begin

subsection {* Determining the first atomic command *}

fun fst_cmd :: "cmd \<Rightarrow> cmd"
where "fst_cmd (c\<^sub>1;;c\<^sub>2) = fst_cmd c\<^sub>1"
  | "fst_cmd c = c"

lemma Proc_CFG_Call_target_fst_cmd_Skip:
  "\<lbrakk>labels prog l' c; prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l'\<rbrakk> 
  \<Longrightarrow> fst_cmd c = Skip"
proof(induct arbitrary:n rule:labels.induct) 
  case (Labels_Seq1 c\<^sub>1 l c c\<^sub>2)
  note IH = `\<And>n. c\<^sub>1 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip`
  from `c\<^sub>1;; c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l` `labels c\<^sub>1 l c`
  have "c\<^sub>1 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases,auto dest:Proc_CFG_Call_Labels)
    by(case_tac n')(auto dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case by simp
next
  case (Labels_Seq2 c\<^sub>2 l c c\<^sub>1)
  note IH = `\<And>n. c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip`
  from `c\<^sub>1;; c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label (l + #:c\<^sub>1)` `labels c\<^sub>2 l c`
  obtain nx where "c\<^sub>2 \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases)
    apply(auto dest:Proc_CFG_targetlabel_less_num_nodes Proc_CFG_Call_Labels)
    by(case_tac n') auto
  from IH[OF this] show ?case by simp
next
  case (Labels_CondTrue c\<^sub>1 l c b c\<^sub>2)
  note IH = `\<And>n. c\<^sub>1 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip`
  from `if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label (l + 1)` `labels c\<^sub>1 l c`
  obtain nx where "c\<^sub>1 \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases,auto)
     apply(case_tac n') apply auto
    by(case_tac n')(auto dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case by simp
next
  case (Labels_CondFalse c\<^sub>2 l c b c\<^sub>1)
  note IH = `\<And>n. c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip`
  from `if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label (l + #:c\<^sub>1 + 1)` 
    `labels c\<^sub>2 l c`
  obtain nx where "c\<^sub>2 \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases,auto)
     apply(case_tac n') apply(auto dest:Proc_CFG_targetlabel_less_num_nodes)
    by(case_tac n') auto
  from IH[OF this] show ?case by simp
next
  case (Labels_WhileBody c' l c b)
  note IH = `\<And>n. c' \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip`
  from `while (b) c' \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label (l + 2)` `labels c' l c`
  obtain nx where "c' \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases,auto)
    by(case_tac n') auto
  from IH[OF this] show ?case by simp
next
  case (Labels_Call px esx retsx)
  from `Call px esx retsx \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label 1`
  show ?case by(fastforce elim:Proc_CFG.cases)
qed(auto dest:Proc_CFG_Call_Labels)


lemma Proc_CFG_Call_source_fst_cmd_Call:
  "\<lbrakk>labels prog l c; prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'\<rbrakk> 
  \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets"
proof(induct arbitrary:n' rule:labels.induct)
  case (Labels_Base c n')
  from `c \<turnstile> Label 0 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'` show ?case
    by(induct c "Label 0" "CEdge (p, es, rets)" n' rule:Proc_CFG.induct) auto
next
  case (Labels_LAss V e n')
  from `V:=e \<turnstile> Label 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'` show ?case
    by(fastforce elim:Proc_CFG.cases)
next
  case (Labels_Seq1 c\<^sub>1 l c c\<^sub>2)
  note IH = `\<And>n'. c\<^sub>1 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' 
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets`
  from `c\<^sub>1;; c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'` `labels c\<^sub>1 l c`
  have "c\<^sub>1 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'"
    apply - apply(erule Proc_CFG.cases,auto dest:Proc_CFG_Call_Labels)
    by(case_tac n)(auto dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case by simp
next
  case (Labels_Seq2 c\<^sub>2 l c c\<^sub>1)
  note IH = `\<And>n'. c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets`
  from `c\<^sub>1;; c\<^sub>2 \<turnstile> Label (l + #:c\<^sub>1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'` `labels c\<^sub>2 l c`
  obtain nx where "c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx"
    apply - apply(erule Proc_CFG.cases)
    apply(auto dest:Proc_CFG_sourcelabel_less_num_nodes Proc_CFG_Call_Labels)
    by(case_tac n) auto
  from IH[OF this] show ?case by simp
next
  case (Labels_CondTrue c\<^sub>1 l c b c\<^sub>2)
  note IH = `\<And>n'. c\<^sub>1 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' 
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets`
  from `if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> Label (l + 1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'` `labels c\<^sub>1 l c`
  obtain nx where "c\<^sub>1 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx"
    apply - apply(erule Proc_CFG.cases,auto)
     apply(case_tac n) apply auto
    by(case_tac n)(auto dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case by simp
next
  case (Labels_CondFalse c\<^sub>2 l c b c\<^sub>1)
  note IH = `\<And>n'. c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' 
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets`
  from `if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> Label  (l + #:c\<^sub>1 + 1)-CEdge (p, es, rets)\<rightarrow>\<^sub>p n'` 
    `labels c\<^sub>2 l c`
  obtain nx where "c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx"
    apply - apply(erule Proc_CFG.cases,auto)
     apply(case_tac n) apply(auto dest:Proc_CFG_sourcelabel_less_num_nodes)
    by(case_tac n) auto
  from IH[OF this] show ?case by simp
next
  case (Labels_WhileBody c' l c b)
  note IH = `\<And>n'. c' \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' 
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets`
  from `while (b) c' \<turnstile> Label (l + 2) -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'` `labels c' l c`
  obtain nx where "c' \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx"
    apply - apply(erule Proc_CFG.cases,auto dest:Proc_CFG_Call_Labels)
    by(case_tac n) auto
  from IH[OF this] show ?case by simp
next
  case (Labels_WhileExit b c' n')
  have "while (b) c' \<turnstile> Label 1 -IEdge \<Up>id\<rightarrow>\<^sub>p Exit" by(rule Proc_CFG_WhileFalseSkip)
  with `while (b) c' \<turnstile> Label 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
  have False by(rule Proc_CFG_Call_Intra_edge_not_same_source)
  thus ?case by simp
next
  case (Labels_Call px esx retsx)
  from `Call px esx retsx \<turnstile> Label 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
  show ?case by(fastforce elim:Proc_CFG.cases)
qed


subsection {* Definition of @{text Def} and @{text Use} sets *}

subsubsection {* @{text ParamDefs} *}

lemma PCFG_CallEdge_THE_rets:
  "prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'
\<Longrightarrow> (THE rets'. \<exists>p' es' n. prog \<turnstile> n -CEdge(p',es',rets')\<rightarrow>\<^sub>p n') = rets"
by(fastforce intro:the_equality dest:Proc_CFG_Call_nodes_eq')


definition ParamDefs_proc :: "cmd \<Rightarrow> label \<Rightarrow> vname list"
  where "ParamDefs_proc c n \<equiv> 
  if (\<exists>n' p' es' rets'. c \<turnstile> n' -CEdge(p',es',rets')\<rightarrow>\<^sub>p n) then 
     (THE rets'. \<exists>p' es' n'. c \<turnstile> n' -CEdge(p',es',rets')\<rightarrow>\<^sub>p n)
  else []"


lemma in_procs_THE_in_procs_cmd:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
  by(fastforce intro:the_equality)


definition ParamDefs :: "wf_prog \<Rightarrow> node \<Rightarrow> vname list"
  where "ParamDefs wfp n \<equiv> let (prog,procs) = Rep_wf_prog wfp; (p,l) = n in
  (if (p = Main) then ParamDefs_proc prog l
   else (if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
         then ParamDefs_proc (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) l
         else []))"


lemma ParamDefs_Main_Return_target:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n -CEdge(p',es,rets)\<rightarrow>\<^sub>p n'\<rbrakk>
  \<Longrightarrow> ParamDefs wfp (Main,n') = rets"
  by(fastforce dest:PCFG_CallEdge_THE_rets simp:ParamDefs_def ParamDefs_proc_def)

lemma ParamDefs_Proc_Return_target:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n -CEdge(p',es,rets)\<rightarrow>\<^sub>p n'"
  shows "ParamDefs wfp (p,n') = rets"
proof -
  from `Rep_wf_prog wfp = (prog,procs)` have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with `(p,ins,outs,c) \<in> set procs` have "p \<noteq> Main" by fastforce
  moreover
  from `well_formed procs` `(p,ins,outs,c) \<in> set procs`
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:PCFG_CallEdge_THE_rets simp:ParamDefs_def ParamDefs_proc_def)
qed

lemma ParamDefs_Main_IEdge_Nil:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'\<rbrakk>
  \<Longrightarrow> ParamDefs wfp (Main,n') = []"
by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_target 
            simp:ParamDefs_def ParamDefs_proc_def)

lemma ParamDefs_Proc_IEdge_Nil:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'"
  shows "ParamDefs wfp (p,n') = []"
proof -
  from `Rep_wf_prog wfp = (prog,procs)` have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with `(p,ins,outs,c) \<in> set procs` have "p \<noteq> Main" by fastforce  
  moreover
  from `well_formed procs` `(p,ins,outs,c) \<in> set procs`
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_target 
                simp:ParamDefs_def ParamDefs_proc_def)
qed

lemma ParamDefs_Main_CEdge_Nil:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n' -CEdge(p',es,rets)\<rightarrow>\<^sub>p n''\<rbrakk>
  \<Longrightarrow> ParamDefs wfp (Main,n') = []"
by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
            simp:ParamDefs_def ParamDefs_proc_def)

lemma ParamDefs_Proc_CEdge_Nil:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n' -CEdge(p',es,rets)\<rightarrow>\<^sub>p n''"
  shows "ParamDefs wfp (p,n') = []"
proof -
  from `Rep_wf_prog wfp = (prog,procs)` have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with `(p,ins,outs,c) \<in> set procs` have "p \<noteq> Main" by fastforce  
  moreover
  from `well_formed procs` `(p,ins,outs,c) \<in> set procs`
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
                simp:ParamDefs_def ParamDefs_proc_def)
qed


lemma assumes "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
  and "(p, ins, outs) \<in> set (lift_procs wfp)"
  shows ParamDefs_length:"length (ParamDefs wfp (targetnode a)) = length outs"
  (is ?length)
  and Return_update:"f' cf cf' = cf'(ParamDefs wfp (targetnode a) [:=] map cf outs)"
  (is ?update)
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastforce simp:wf_prog_def)
  hence "wf prog procs" by(rule wf_wf_prog)
  hence wf:"well_formed procs" by fastforce
  from assms have "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    by(simp add:valid_edge_def)
  from this `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` wf have "?length \<and> ?update"
  proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
    case (MainReturn l p' es rets l' insx outsx cx)
    from `\<lambda>cf. snd cf = (Main, Label l')\<hookleftarrow>\<^bsub>p'\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outsx) =
      kind a` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have "p' = p" 
      and f':"f' = (\<lambda>cf cf'. cf'(rets [:=] map cf outsx))" by simp_all
    with `well_formed procs` `(p', insx, outsx, cx) \<in> set procs`
      `(p, ins, outs) \<in> set (lift_procs wfp)`
    have [simp]:"outsx = outs" by fastforce
    from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
    have "containsCall procs prog [] p'" by(rule Proc_CFG_Call_containsCall)
    with `wf prog procs` `(p', insx, outsx, cx) \<in> set procs` 
      `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
    have "length rets = length outs" by fastforce
    from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
    have "ParamDefs wfp (Main,Label l') = rets"
      by(fastforce intro:ParamDefs_Main_Return_target)
    with `(Main, Label l') = targetnode a` f' `length rets = length outs`
    show ?thesis by simp
  next
    case (ProcReturn px insx outsx cx l p' es rets l' ins' outs' c' ps)
    from `\<lambda>cf. snd cf = (px, Label l')\<hookleftarrow>\<^bsub>p'\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs') =
      kind a` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
    have "p' = p" and f':"f' = (\<lambda>cf cf'. cf'(rets [:=] map cf outs'))"
      by simp_all
    with `well_formed procs` `(p', ins', outs', c') \<in> set procs`
      `(p, ins, outs) \<in> set (lift_procs wfp)`
    have [simp]:"outs' = outs" by fastforce
    from `cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
    have "containsCall procs cx [] p'" by(rule Proc_CFG_Call_containsCall)
    with `containsCall procs prog ps px` `(px, insx, outsx, cx) \<in> set procs`
    have "containsCall procs prog (ps@[px]) p'" by(rule containsCall_in_proc)
    with `wf prog procs` `(p', ins', outs', c') \<in> set procs`
      `cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
    have "length rets = length outs" by fastforce
    from `(px, insx, outsx, cx) \<in> set procs`
      `cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
    have "ParamDefs wfp (px,Label l') = rets"
      by(fastforce intro:ParamDefs_Proc_Return_target simp:set_conv_nth)
    with `(px, Label l') = targetnode a` f' `length rets = length outs`
    show ?thesis by simp
  qed auto
  thus "?length" and "?update" by simp_all
qed


subsubsection {* @{text ParamUses} *}

fun fv :: "expr \<Rightarrow> vname set"
where
  "fv (Val v)       = {}"
  | "fv (Var V)       = {V}"
  | "fv (e1 \<guillemotleft>bop\<guillemotright> e2) = (fv e1 \<union> fv e2)"


lemma rhs_interpret_eq: 
  "\<lbrakk>state_check cf e v'; \<forall>V \<in> fv e. cf V = cf' V\<rbrakk> 
   \<Longrightarrow> state_check cf' e v'"
proof(induct e arbitrary:v')
  case (Val v)
  from `state_check cf (Val v) v'` have "v' = Some v" 
    by(fastforce elim:interpret.cases)
  thus ?case by simp
next
  case (Var V)
  hence "cf' (V) = v'" by(fastforce elim:interpret.cases)
  thus ?case by simp
next
  case (BinOp b1 bop b2)
  note IH1 = `\<And>v'. \<lbrakk>state_check cf b1 v'; \<forall>V\<in>fv b1. cf V = cf' V\<rbrakk>
    \<Longrightarrow> state_check cf' b1 v'`
  note IH2 = `\<And>v'. \<lbrakk>state_check cf b2 v'; \<forall>V\<in>fv b2. cf V = cf' V\<rbrakk>
    \<Longrightarrow> state_check cf' b2 v'`
  from `\<forall>V \<in> fv (b1 \<guillemotleft>bop\<guillemotright> b2). cf V = cf' V` have "\<forall>V \<in> fv b1. cf V = cf' V"
    and "\<forall>V \<in> fv b2. cf V = cf' V" by simp_all
  from `state_check cf (b1 \<guillemotleft>bop\<guillemotright> b2) v'`
  have "((state_check cf b1 None \<and> v' = None) \<or> 
          (state_check cf b2 None \<and> v' = None)) \<or>
    (\<exists>v\<^sub>1 v\<^sub>2. state_check cf b1 (Some v\<^sub>1) \<and> state_check cf b2 (Some v\<^sub>2) \<and>
    binop bop v\<^sub>1 v\<^sub>2 = v')"
    apply(cases "interpret b1 cf",simp)
    apply(cases "interpret b2 cf",simp)
    by(case_tac "binop bop a aa",simp+)
  thus ?case apply - 
  proof(erule disjE)+
    assume "state_check cf b1 None \<and> v' = None"
    hence check:"state_check cf b1 None" and "v' = None" by simp_all
    from IH1[OF check `\<forall>V \<in> fv b1. cf V = cf' V`] have "state_check cf' b1 None" .
    with `v' = None` show ?case by simp
  next
    assume "state_check cf b2 None \<and> v' = None"
    hence check:"state_check cf b2 None" and "v' = None" by simp_all
    from IH2[OF check `\<forall>V \<in> fv b2. cf V = cf' V`] have "state_check cf' b2 None" .
    with `v' = None` show ?case by(cases "interpret b1 cf'") simp+
  next
    assume "\<exists>v\<^sub>1 v\<^sub>2. state_check cf b1 (Some v\<^sub>1) \<and>
      state_check cf b2 (Some v\<^sub>2) \<and> binop bop v\<^sub>1 v\<^sub>2 = v'"
    then obtain v\<^sub>1 v\<^sub>2 where "state_check cf b1 (Some v\<^sub>1)"
      and "state_check cf b2 (Some v\<^sub>2)" and "binop bop v\<^sub>1 v\<^sub>2 = v'" by blast
    from `\<forall>V \<in> fv (b1 \<guillemotleft>bop\<guillemotright> b2). cf V = cf' V` have "\<forall>V \<in> fv b1. cf V = cf' V"
      by simp
    from IH1[OF `state_check cf b1 (Some v\<^sub>1)` this]
    have "interpret b1 cf' = Some v\<^sub>1" .
    from `\<forall>V \<in> fv (b1 \<guillemotleft>bop\<guillemotright> b2). cf V = cf' V` have "\<forall>V \<in> fv b2. cf V = cf' V"
      by simp
    from IH2[OF `state_check cf b2 (Some v\<^sub>2)` this] 
    have "interpret b2 cf' = Some v\<^sub>2" .
    with `interpret b1 cf' = Some v\<^sub>1` `binop bop v\<^sub>1 v\<^sub>2 = v'`
    show ?thesis by(cases v') simp+
  qed
qed



lemma PCFG_CallEdge_THE_es:
  "prog \<turnstile> n -CEdge(p,es,rets)\<rightarrow>\<^sub>p n'
\<Longrightarrow> (THE es'. \<exists>p' rets' n'. prog \<turnstile> n -CEdge(p',es',rets')\<rightarrow>\<^sub>p n') = es"
by(fastforce intro:the_equality dest:Proc_CFG_Call_nodes_eq)


definition ParamUses_proc :: "cmd \<Rightarrow> label \<Rightarrow> vname set list"
  where "ParamUses_proc c n \<equiv>
  if (\<exists>n' p' es' rets'. c \<turnstile> n -CEdge(p',es',rets')\<rightarrow>\<^sub>p n') then 
  (map fv (THE es'. \<exists>p' rets' n'. c \<turnstile> n -CEdge(p',es',rets')\<rightarrow>\<^sub>p n'))
  else []"


definition ParamUses :: "wf_prog \<Rightarrow> node \<Rightarrow> vname set list"
  where "ParamUses wfp n \<equiv> let (prog,procs) = Rep_wf_prog wfp; (p,l) = n in
  (if (p = Main) then ParamUses_proc prog l
   else (if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
         then ParamUses_proc (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) l
         else []))"


lemma ParamUses_Main_Return_target:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n -CEdge(p',es,rets)\<rightarrow>\<^sub>p n' \<rbrakk>
  \<Longrightarrow> ParamUses wfp (Main,n) = map fv es"
  by(fastforce dest:PCFG_CallEdge_THE_es simp:ParamUses_def ParamUses_proc_def)

lemma ParamUses_Proc_Return_target:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n -CEdge(p',es,rets)\<rightarrow>\<^sub>p n'"
  shows "ParamUses wfp (p,n) = map fv es"
proof -
  from `Rep_wf_prog wfp = (prog,procs)` have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with `(p,ins,outs,c) \<in> set procs` have "p \<noteq> Main" by fastforce  
  moreover
  from `well_formed procs` `(p,ins,outs,c) \<in> set procs`
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:PCFG_CallEdge_THE_es simp:ParamUses_def ParamUses_proc_def)
qed

lemma ParamUses_Main_IEdge_Nil:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'\<rbrakk>
  \<Longrightarrow> ParamUses wfp (Main,n) = []"
by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_source
            simp:ParamUses_def ParamUses_proc_def)

lemma ParamUses_Proc_IEdge_Nil:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'"
  shows "ParamUses wfp (p,n) = []"
proof -
  from `Rep_wf_prog wfp = (prog,procs)` have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with `(p,ins,outs,c) \<in> set procs` have "p \<noteq> Main" by fastforce  
  moreover
  from `well_formed procs` `(p,ins,outs,c) \<in> set procs`
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_source
                simp:ParamUses_def ParamUses_proc_def)
qed

lemma ParamUses_Main_CEdge_Nil:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n' -CEdge(p',es,rets)\<rightarrow>\<^sub>p n\<rbrakk>
  \<Longrightarrow> ParamUses wfp (Main,n) = []"
by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
            simp:ParamUses_def ParamUses_proc_def)

lemma ParamUses_Proc_CEdge_Nil:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n' -CEdge(p',es,rets)\<rightarrow>\<^sub>p n"
  shows "ParamUses wfp (p,n) = []"
proof -
  from `Rep_wf_prog wfp = (prog,procs)` have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with `(p,ins,outs,c) \<in> set procs` have "p \<noteq> Main" by fastforce  
  moreover
  from `well_formed procs` 
    `(p,ins,outs,c) \<in> set procs`
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
                simp:ParamUses_def ParamUses_proc_def)
qed


subsubsection {* @{text Def} *}

fun lhs :: "cmd \<Rightarrow> vname set"
where
  "lhs Skip                = {}"
  | "lhs (V:=e)              = {V}"
  | "lhs (c\<^sub>1;;c\<^sub>2)            = lhs c\<^sub>1"
  | "lhs (if (b) c\<^sub>1 else c\<^sub>2) = {}"
  | "lhs (while (b) c)       = {}"
  | "lhs (Call p es rets)    = {}"

lemma lhs_fst_cmd:"lhs (fst_cmd c) = lhs c" by(induct c) auto

lemma Proc_CFG_Call_source_empty_lhs:
  assumes "prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'"
  shows "lhs (label prog l) = {}"
proof -
  from `prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'` have "l < #:prog"
    by(rule Proc_CFG_sourcelabel_less_num_nodes)
  then obtain c' where "labels prog l c'"
    by(erule less_num_inner_nodes_label)
  hence "label prog l = c'" by(rule labels_label)
  from `labels prog l c'` `prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'`
  have "\<exists>p es rets. fst_cmd c' = Call p es rets" 
    by(rule Proc_CFG_Call_source_fst_cmd_Call)
  with lhs_fst_cmd[of c'] have "lhs c' = {}" by auto
  with `label prog l = c'` show ?thesis by simp
qed


lemma in_procs_THE_in_procs_ins:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE ins'. \<exists>c' outs'. (p,ins',outs',c') \<in> set procs) = ins"
  by(fastforce intro:the_equality)


definition Def :: "wf_prog \<Rightarrow> node \<Rightarrow> vname set"
  where "Def wfp n \<equiv> (let (prog,procs) = Rep_wf_prog wfp; (p,l) = n in
  (case l of Label lx \<Rightarrow> 
    (if p = Main then lhs (label prog lx)
     else (if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
           then 
  lhs (label (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) lx)
           else {}))
  | Entry \<Rightarrow> if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
            then (set 
      (THE ins'. \<exists>c' outs'. (p,ins',outs',c') \<in> set procs)) else {}
  | Exit \<Rightarrow> {}))
    \<union> set (ParamDefs wfp n)"

lemma Entry_Def_empty:"Def wfp (Main, Entry) = {}"
proof -
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)"
    by(cases "Rep_wf_prog wfp") auto
  hence "well_formed procs" by(fastforce intro:wf_wf_prog)
  thus ?thesis by(auto simp:Def_def ParamDefs_def ParamDefs_proc_def)
qed


lemma Exit_Def_empty:"Def wfp (Main, Exit) = {}"
  proof -
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)"
    by(cases "Rep_wf_prog wfp") auto
  hence "well_formed procs" by(fastforce intro:wf_wf_prog)
  thus ?thesis 
    by(auto dest:Proc_CFG_Call_Labels simp:Def_def ParamDefs_def ParamDefs_proc_def)
qed



subsubsection {* @{text Use} *}

fun rhs :: "cmd \<Rightarrow> vname set"
where
  "rhs Skip                = {}"
  | "rhs (V:=e)              = fv e"
  | "rhs (c\<^sub>1;;c\<^sub>2)            = rhs c\<^sub>1"
  | "rhs (if (b) c\<^sub>1 else c\<^sub>2) = fv b"
  | "rhs (while (b) c)       = fv b"
  | "rhs (Call p es rets)    = {}"

lemma rhs_fst_cmd:"rhs (fst_cmd c) = rhs c" by(induct c) auto

lemma Proc_CFG_Call_target_empty_rhs:
  assumes "prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l'"
  shows "rhs (label prog l') = {}"
proof -
  from `prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l'` have "l' < #:prog"
    by(rule Proc_CFG_targetlabel_less_num_nodes)
  then obtain c' where "labels prog l' c'"
    by(erule less_num_inner_nodes_label)
  hence "label prog l' = c'" by(rule labels_label)
  from `labels prog l' c'` `prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l'`
  have "fst_cmd c' = Skip" by(rule Proc_CFG_Call_target_fst_cmd_Skip)
  with rhs_fst_cmd[of c'] have "rhs c' = {}" by simp
  with `label prog l' = c'` show ?thesis by simp
qed



lemma in_procs_THE_in_procs_outs:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE outs'. \<exists>c' ins'. (p,ins',outs',c') \<in> set procs) = outs"
  by(fastforce intro:the_equality)


definition Use :: "wf_prog \<Rightarrow> node \<Rightarrow> vname set"
  where "Use wfp n \<equiv> (let (prog,procs) = Rep_wf_prog wfp; (p,l) = n in
  (case l of Label lx \<Rightarrow> 
    (if p = Main then rhs (label prog lx) 
     else (if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
           then 
  rhs (label (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) lx)
           else {}))
  | Exit \<Rightarrow> if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
            then (set (THE outs'. \<exists>c' ins'. (p,ins',outs',c') \<in> set procs) )
            else {}
  | Entry \<Rightarrow> if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
      then (set (THE ins'. \<exists>c' outs'. (p,ins',outs',c') \<in> set procs))
      else {}))
  \<union> Union (set (ParamUses wfp n)) \<union> set (ParamDefs wfp n)"


lemma Entry_Use_empty:"Use wfp (Main, Entry) = {}"
proof -
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)"
    by(cases "Rep_wf_prog wfp") auto
  hence "well_formed procs" by(fastforce intro:wf_wf_prog)
  thus ?thesis by(auto dest:Proc_CFG_Call_Labels 
    simp:Use_def ParamUses_def ParamUses_proc_def ParamDefs_def ParamDefs_proc_def)
qed

lemma Exit_Use_empty:"Use wfp (Main, Exit) = {}"
proof -
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)"
    by(cases "Rep_wf_prog wfp") auto
  hence "well_formed procs" by(fastforce intro:wf_wf_prog)
  thus ?thesis by(auto dest:Proc_CFG_Call_Labels 
    simp:Use_def ParamUses_def ParamUses_proc_def ParamDefs_def ParamDefs_proc_def)
qed


subsection {* Lemmas about edges and call frames *}

lemmas transfers_simps = ProcCFG.transfer.simps[simplified]
declare transfers_simps [simp]

abbreviation state_val :: "(('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'var \<rightharpoonup> 'val"
  where "state_val s V \<equiv> (fst (hd s)) V"

lemma Proc_CFG_edge_no_lhs_equal:
  assumes "prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'" and "V \<notin> lhs (label prog l)"
  shows "state_val (CFG.transfer (lift_procs wfp) et (cf#cfs)) V = fst cf V"
proof -
  from `prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'` 
  obtain x where "IEdge et = x" and "prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'" by simp_all
  from `prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'` `IEdge et = x` `V \<notin> lhs (label prog l)`
  show ?thesis
  proof(induct prog "Label l" x n' arbitrary:l rule:Proc_CFG.induct)
    case (Proc_CFG_LAss V' e)
    have "labels (V':=e) 0 (V':=e)" by(rule Labels_Base)
    hence "label (V':=e) 0 = (V':=e)" by(rule labels_label)
    have "V' \<in> lhs (V':=e)" by simp
    with `V \<notin> lhs (label (V':=e) 0)`
      `IEdge et = IEdge \<Up>\<lambda>cf. update cf V' e` `label (V':=e) 0 = (V':=e)`
    show ?case by fastforce
  next
    case (Proc_CFG_SeqFirst c\<^sub>1 et' n' c\<^sub>2)
    note IH = `\<lbrakk>IEdge et = et'; V \<notin> lhs (label c\<^sub>1 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V`
    from `c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p n'` have "l < #:c\<^sub>1"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    hence "label (c\<^sub>1;;c\<^sub>2) l = c';;c\<^sub>2" by(rule labels_label)
    with `V \<notin> lhs (label (c\<^sub>1;; c\<^sub>2) l)` `labels c\<^sub>1 l c'` 
    have "V \<notin> lhs (label c\<^sub>1 l)" by(fastforce dest:labels_label)
    with `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_SeqConnect c\<^sub>1 et' c\<^sub>2)
    note IH = `\<lbrakk>IEdge et = et'; V \<notin> lhs (label c\<^sub>1 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V`
    from `c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p Exit` have "l < #:c\<^sub>1"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    hence "label (c\<^sub>1;;c\<^sub>2) l = c';;c\<^sub>2" by(rule labels_label)
    with `V \<notin> lhs (label (c\<^sub>1;; c\<^sub>2) l)` `labels c\<^sub>1 l c'` 
    have "V \<notin> lhs (label c\<^sub>1 l)" by(fastforce dest:labels_label)
    with `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_SeqSecond c\<^sub>2 n et' n' c\<^sub>1 l)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c\<^sub>2 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V`
    from `n \<oplus> #:c\<^sub>1 = Label l` obtain l' 
      where "n = Label l'" and "l = l' + #:c\<^sub>1" by(cases n) auto
    from `n = Label l'` `c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` have "l' < #:c\<^sub>2"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + #:c\<^sub>1` have "labels (c\<^sub>1;;c\<^sub>2) l c'" 
      by(fastforce intro:Labels_Seq2)
    hence "label (c\<^sub>1;;c\<^sub>2) l = c'" by(rule labels_label)
    with `V \<notin> lhs (label (c\<^sub>1;;c\<^sub>2) l)` `labels c\<^sub>2 l' c'` `l = l' + #:c\<^sub>1`
    have "V \<notin> lhs (label c\<^sub>2 l')" by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_CondThen c\<^sub>1 n et' n' b c\<^sub>2 l)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c\<^sub>1 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V`
    from `n \<oplus> 1 = Label l` obtain l' 
      where "n = Label l'" and "l = l' + 1" by(cases n) auto
    from `n = Label l'` `c\<^sub>1 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` have "l' < #:c\<^sub>1"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + 1` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondTrue)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) l = c'" by(rule labels_label)
    with `V \<notin> lhs (label (if (b) c\<^sub>1 else c\<^sub>2) l)` `labels c\<^sub>1 l' c'` `l = l' + 1`
    have "V \<notin> lhs (label c\<^sub>1 l')" by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_CondElse c\<^sub>2 n et' n' b c\<^sub>1 l)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c\<^sub>2 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V`
    from `n \<oplus> #:c\<^sub>1 + 1 = Label l` obtain l' 
      where "n = Label l'" and "l = l' + #:c\<^sub>1 + 1" by(cases n) auto
    from `n = Label l'` `c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` have "l' < #:c\<^sub>2"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + #:c\<^sub>1 + 1` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondFalse)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) l = c'" by(rule labels_label)
    with `V \<notin> lhs (label (if (b) c\<^sub>1 else c\<^sub>2) l)` `labels c\<^sub>2 l' c'` `l = l' + #:c\<^sub>1 + 1`
    have "V \<notin> lhs (label c\<^sub>2 l')" by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_WhileBody c' n et' n' b l)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c' l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V`
    from `n \<oplus> 2 = Label l` obtain l' 
      where "n = Label l'" and "l = l' + 2" by(cases n) auto
    from `n = Label l'` `c' \<turnstile> n -et'\<rightarrow>\<^sub>p n'` have "l' < #:c'"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with `l = l' + 2` have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    hence "label (while (b) c') l = cx;;while (b) c'" by(rule labels_label)
    with `V \<notin> lhs (label (while (b) c') l)` `labels c' l' cx` `l = l' + 2`
    have "V \<notin> lhs (label c' l')" by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_WhileBodyExit c' n et' b l)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c' l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V`
    from `n \<oplus> 2 = Label l` obtain l' 
      where "n = Label l'" and "l = l' + 2" by(cases n) auto
    from `n = Label l'` `c' \<turnstile> n -et'\<rightarrow>\<^sub>p Exit` have "l' < #:c'"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with `l = l' + 2` have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    hence "label (while (b) c') l = cx;;while (b) c'" by(rule labels_label)
    with `V \<notin> lhs (label (while (b) c') l)` `labels c' l' cx` `l = l' + 2`
    have "V \<notin> lhs (label c' l')" by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  qed auto
qed



lemma Proc_CFG_edge_uses_only_rhs:
  assumes "prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'" and "CFG.pred et s"
  and "CFG.pred et s'" and "\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V"
  shows "\<forall>V\<in>lhs (label prog l). 
    state_val (CFG.transfer (lift_procs wfp) et s) V =
    state_val (CFG.transfer (lift_procs wfp) et s') V"
proof -
  from `prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'` 
  obtain x where "IEdge et = x" and "prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'" by simp_all
  from `CFG.pred et s` obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
  from `CFG.pred et s'` obtain cf' cfs' where [simp]:"s' = cf'#cfs'" 
    by(cases s') auto
  from `prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'` `IEdge et = x`
    `\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V`
  show ?thesis
  proof(induct prog "Label l" x n' arbitrary:l rule:Proc_CFG.induct)
    case Proc_CFG_Skip
    have "labels Skip 0 Skip" by(rule Labels_Base)
    hence "label Skip 0 = Skip" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label Skip 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_LAss V e)
    have "labels (V:=e) 0 (V:=e)" by(rule Labels_Base)
    hence "label (V:=e) 0 = V:=e" by(rule labels_label)
    then have "lhs (label (V:=e) 0) = {V}"
      and "rhs (label (V:=e) 0) = fv e" by auto
    with `IEdge et = IEdge \<Up>\<lambda>cf. update cf V e` 
      `\<forall>V\<in>rhs (label (V:=e) 0). state_val s V = state_val s' V`
    show ?case by(fastforce intro:rhs_interpret_eq)
  next
    case (Proc_CFG_LAssSkip V e)
    have "labels (V:=e) 1 Skip" by(rule Labels_LAss)
    hence "label (V:=e) 1 = Skip" by(rule labels_label)
    hence "\<forall>V'. V' \<notin> lhs (label (V:=e) 1)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_SeqFirst c\<^sub>1 et' n' c\<^sub>2)
    note IH = `\<lbrakk>IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V`
    from `c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p n'`
    have "l < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    with `labels c\<^sub>1 l c'` `\<forall>V\<in>rhs (label (c\<^sub>1;; c\<^sub>2) l). state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with `IEdge et = et'`
    have "\<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with `labels c\<^sub>1 l c'` `labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)`
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_SeqConnect c\<^sub>1 et' c\<^sub>2)
    note IH = `\<lbrakk>IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V`
    from `c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p Exit`
    have "l < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    with `labels c\<^sub>1 l c'` `\<forall>V\<in>rhs (label (c\<^sub>1;; c\<^sub>2) l). state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with `IEdge et = et'`
    have "\<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with `labels c\<^sub>1 l c'` `labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)`
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_SeqSecond c\<^sub>2 n et' n' c\<^sub>1)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>2 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>2 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V`
    from `n \<oplus> #:c\<^sub>1 = Label l` obtain l' where "n = Label l'" and "l = l' + #:c\<^sub>1"
      by(cases n) auto
    from `c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` `n = Label l'`
    have "l' < #:c\<^sub>2" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + #:c\<^sub>1` have "labels (c\<^sub>1;;c\<^sub>2) l c'" by(fastforce intro:Labels_Seq2)
    with `labels c\<^sub>2 l' c'` `\<forall>V\<in>rhs (label (c\<^sub>1;;c\<^sub>2) l). state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>2 l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'`
    have "\<forall>V\<in>lhs (label c\<^sub>2 l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with `labels c\<^sub>2 l' c'` `labels (c\<^sub>1;;c\<^sub>2) l c'`
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_CondTrue b c\<^sub>1 c\<^sub>2)
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)" by(rule Labels_Base)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) 0 = if (b) c\<^sub>1 else c\<^sub>2" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (if (b) c\<^sub>1 else c\<^sub>2) 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_CondFalse b c\<^sub>1 c\<^sub>2)
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)" by(rule Labels_Base)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) 0 = if (b) c\<^sub>1 else c\<^sub>2" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (if (b) c\<^sub>1 else c\<^sub>2) 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_CondThen c\<^sub>1 n et' n' b c\<^sub>2)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V`
    from `n \<oplus> 1 = Label l` obtain l' where "n = Label l'" and "l = l' + 1"
      by(cases n) auto
    from `c\<^sub>1 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` `n = Label l'`
    have "l' < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + 1` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondTrue)
    with `labels c\<^sub>1 l' c'` `\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) l). state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>1 l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'`
    have "\<forall>V\<in>lhs (label c\<^sub>1 l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with `labels c\<^sub>1 l' c'` `labels (if (b) c\<^sub>1 else c\<^sub>2) l c'`
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_CondElse c\<^sub>2 n et' n' b c\<^sub>1)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c\<^sub>2 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>2 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V`
    from `n \<oplus> #:c\<^sub>1 + 1= Label l` obtain l' where "n = Label l'" and "l = l' + #:c\<^sub>1+1"
      by(cases n) auto
    from `c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` `n = Label l'`
    have "l' < #:c\<^sub>2" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + #:c\<^sub>1 + 1` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondFalse)
    with `labels c\<^sub>2 l' c'` `\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) l). 
      state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>2 l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'`
    have "\<forall>V\<in>lhs (label c\<^sub>2 l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with `labels c\<^sub>2 l' c'` `labels (if (b) c\<^sub>1 else c\<^sub>2) l c'`
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_WhileTrue b c')
    have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
    hence "label (while (b) c') 0 = while (b) c'" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (while (b) c') 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_WhileFalse b c')
    have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
    hence "label (while (b) c') 0 = while (b) c'" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (while (b) c') 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_WhileFalseSkip b c')
    have "labels (while (b) c') 1 Skip" by(rule Labels_WhileExit)
    hence "label (while (b) c') 1 = Skip" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (while (b) c') 1)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_WhileBody c' n et' n' b)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c' l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c' l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V`
    from `n \<oplus> 2 = Label l` obtain l' where "n = Label l'" and "l = l' + 2"
      by(cases n) auto
    from `c' \<turnstile> n -et'\<rightarrow>\<^sub>p n'` `n = Label l'`
    have "l' < #:c'" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with `l = l' + 2` have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    with `labels c' l' cx` `\<forall>V\<in>rhs (label (while (b) c') l). 
      state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c' l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'`
    have "\<forall>V\<in>lhs (label c' l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with `labels c' l' cx` `labels (while (b) c') l (cx;;while (b) c')`
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_WhileBodyExit c' n et' b)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c' l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c' l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V`
    from `n \<oplus> 2 = Label l` obtain l' where "n = Label l'" and "l = l' + 2"
      by(cases n) auto
    from `c' \<turnstile> n -et'\<rightarrow>\<^sub>p Exit` `n = Label l'`
    have "l' < #:c'" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with `l = l' + 2` have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    with `labels c' l' cx` `\<forall>V\<in>rhs (label (while (b) c') l).
      state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c' l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'`
    have "\<forall>V\<in>lhs (label c' l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with `labels c' l' cx` `labels (while (b) c') l (cx;;while (b) c')`
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_CallSkip p es rets)
    have "labels (Call p es rets) 1 Skip" by(rule Labels_Call)
    hence "label (Call p es rets) 1 = Skip" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (Call p es rets) 1)" by simp
    then show ?case by fastforce
  qed auto
qed


lemma Proc_CFG_edge_rhs_pred_eq:
  assumes "prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'" and "CFG.pred et s"
  and "\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V"
  and "length s = length s'"
  shows "CFG.pred et s'"
proof -
  from `prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'` 
  obtain x where "IEdge et = x" and "prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'" by simp_all
  from `CFG.pred et s` obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
  from `length s = length s'` obtain cf' cfs' where [simp]:"s' = cf'#cfs'" 
    by(cases s') auto
  from `prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'` `IEdge et = x` 
    `\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V`
  show ?thesis
  proof(induct prog "Label l" x n' arbitrary:l rule:Proc_CFG.induct)
    case (Proc_CFG_SeqFirst c\<^sub>1 et' n' c\<^sub>2)
    note IH = `\<lbrakk>IEdge et = et'; \<forall>V\<in>rhs (label c\<^sub>1 l). 
      state_val s V = state_val s' V\<rbrakk> \<Longrightarrow> CFG.pred et s'`
    from `c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p n'`
    have "l < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    with `labels c\<^sub>1 l c'` `\<forall>V\<in>rhs (label (c\<^sub>1;; c\<^sub>2) l). state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_SeqConnect c\<^sub>1 et' c\<^sub>2)
    note IH = `\<lbrakk>IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> CFG.pred et s'`
    from `c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p Exit`
    have "l < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    with `labels c\<^sub>1 l c'` `\<forall>V\<in>rhs (label (c\<^sub>1;; c\<^sub>2) l). state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_SeqSecond c\<^sub>2 n et' n' c\<^sub>1)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c\<^sub>2 l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'`
    from `n \<oplus> #:c\<^sub>1 = Label l` obtain l' where "n = Label l'" and "l = l' + #:c\<^sub>1"
      by(cases n) auto
    from `c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` `n = Label l'`
    have "l' < #:c\<^sub>2" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + #:c\<^sub>1` have "labels (c\<^sub>1;;c\<^sub>2) l c'" by(fastforce intro:Labels_Seq2)
    with `labels c\<^sub>2 l' c'` `\<forall>V\<in>rhs (label (c\<^sub>1;;c\<^sub>2) l). state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>2 l'). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_CondTrue b c\<^sub>1 c\<^sub>2)
    from `CFG.pred et s` `IEdge et = IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>`
    have "state_check (fst cf) b (Some true)" by simp
    moreover
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)" by(rule Labels_Base)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) 0 = if (b) c\<^sub>1 else c\<^sub>2" by(rule labels_label)
    with `\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) 0). state_val s V = state_val s' V`
    have "\<forall>V\<in> fv b. state_val s V = state_val s' V" by fastforce
    ultimately have "state_check (fst cf') b (Some true)" 
      by simp(rule rhs_interpret_eq)
    with `IEdge et = IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>`
    show ?case by simp
  next
    case (Proc_CFG_CondFalse b c\<^sub>1 c\<^sub>2)
    from `CFG.pred et s` 
      `IEdge et = IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>`
    have "state_check (fst cf) b (Some false)" by simp
    moreover
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)" by(rule Labels_Base)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) 0 = if (b) c\<^sub>1 else c\<^sub>2" by(rule labels_label)
    with `\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) 0). state_val s V = state_val s' V`
    have "\<forall>V\<in> fv b. state_val s V = state_val s' V" by fastforce
    ultimately have "state_check (fst cf') b (Some false)" 
      by simp(rule rhs_interpret_eq)
    with `IEdge et = IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>` 
    show ?case by simp
  next
    case (Proc_CFG_CondThen c\<^sub>1 n et' n' b c\<^sub>2)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'`
    from `n \<oplus> 1 = Label l` obtain l' where "n = Label l'" and "l = l' + 1"
      by(cases n) auto
    from `c\<^sub>1 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` `n = Label l'`
    have "l' < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + 1` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondTrue)
    with `labels c\<^sub>1 l' c'` `\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) l). 
      state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>1 l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_CondElse c\<^sub>2 n et' n' b c\<^sub>1)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c\<^sub>2 l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'`
    from `n \<oplus> #:c\<^sub>1 + 1= Label l` obtain l' where "n = Label l'" and "l = l' + #:c\<^sub>1+1"
      by(cases n) auto
    from `c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'` `n = Label l'`
    have "l' < #:c\<^sub>2" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with `l = l' + #:c\<^sub>1 + 1` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondFalse)
    with `labels c\<^sub>2 l' c'` `\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) l). 
      state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c\<^sub>2 l'). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_WhileTrue b c')
    from `CFG.pred et s` `IEdge et = IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>`
    have "state_check (fst cf) b (Some true)" by simp
    moreover
    have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
    hence "label (while (b) c') 0 = while (b) c'" by(rule labels_label)
    with `\<forall>V\<in>rhs (label (while (b) c') 0). state_val s V = state_val s' V` 
    have "\<forall>V\<in> fv b. state_val s V = state_val s' V" by fastforce
    ultimately have "state_check (fst cf') b (Some true)" 
      by simp(rule rhs_interpret_eq)
    with `IEdge et = IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>`
    show ?case by simp
  next
    case (Proc_CFG_WhileFalse b c')
    from `CFG.pred et s`
      `IEdge et = IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>`
    have "state_check (fst cf) b (Some false)" by simp
    moreover
    have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
    hence "label (while (b) c') 0 = while (b) c'" by(rule labels_label)
    with `\<forall>V\<in>rhs (label (while (b) c') 0). state_val s V = state_val s' V` 
    have "\<forall>V\<in> fv b. state_val s V = state_val s' V" by fastforce
    ultimately have "state_check (fst cf') b (Some false)" 
      by simp(rule rhs_interpret_eq)
    with `IEdge et = IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>`
    show ?case by simp
  next
    case (Proc_CFG_WhileBody c' n et' n' b)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c' l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'`
    from `n \<oplus> 2 = Label l` obtain l' where "n = Label l'" and "l = l' + 2"
      by(cases n) auto
    from `c' \<turnstile> n -et'\<rightarrow>\<^sub>p n'` `n = Label l'`
    have "l' < #:c'" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with `l = l' + 2` have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    with `labels c' l' cx` `\<forall>V\<in>rhs (label (while (b) c') l). 
      state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c' l'). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  next
    case (Proc_CFG_WhileBodyExit c' n et' b)
    note IH = `\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c' l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'`
    from `n \<oplus> 2 = Label l` obtain l' where "n = Label l'" and "l = l' + 2"
      by(cases n) auto
    from `c' \<turnstile> n -et'\<rightarrow>\<^sub>p Exit` `n = Label l'`
    have "l' < #:c'" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with `l = l' + 2` have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    with `labels c' l' cx` `\<forall>V\<in>rhs (label (while (b) c') l). 
      state_val s V = state_val s' V`
    have "\<forall>V\<in>rhs (label c' l'). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with `n = Label l'` `IEdge et = et'` show ?case by (rule IH)
  qed auto
qed



subsection {* Instantiating the @{text CFG_wf} locale *}

interpretation ProcCFG_wf:
  CFG_wf sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main 
  "Def wfp" "Use wfp" "ParamDefs wfp" "ParamUses wfp"
  for wfp
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastforce simp:wf_prog_def)
  hence "wf prog procs" by(rule wf_wf_prog)
  hence wf:"well_formed procs" by fastforce
  show "CFG_wf sourcenode targetnode kind (valid_edge wfp)
    (Main, Entry) get_proc (get_return_edges wfp) (lift_procs wfp) Main 
    (Def wfp) (Use wfp) (ParamDefs wfp) (ParamUses wfp)"
  proof
    from Entry_Def_empty Entry_Use_empty
    show "Def wfp (Main, Entry) = {} \<and> Use wfp (Main, Entry) = {}" by simp
  next
    fix a Q r p fs ins outs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p, ins, outs) \<in> set (lift_procs wfp)`
    show "length (ParamUses wfp (sourcenode a)) = length ins"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' insx outsx cx)
      with wf have [simp]:"insx = ins" by fastforce
      from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "containsCall procs prog [] p'" by(rule Proc_CFG_Call_containsCall)
      with `wf prog procs` `(p', insx, outsx, cx) \<in> set procs` 
        `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "length es = length ins" by fastforce
      from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "ParamUses wfp (Main, Label l) = map fv es"
        by(fastforce intro:ParamUses_Main_Return_target)
      with `(Main, Label l) = sourcenode a` `length es = length ins`
      show ?case by simp
    next
      case (ProcCall px insx outsx cx l p' es rets l' ins' outs' c' ps)
      with wf have [simp]:"ins' = ins" by fastforce
      from `cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
      have "containsCall procs cx [] p'" by(rule Proc_CFG_Call_containsCall)
      with `containsCall procs prog ps px` `(px, insx, outsx, cx) \<in> set procs`
      have "containsCall procs prog (ps@[px]) p'" by(rule containsCall_in_proc)
      with `wf prog procs` `(p', ins', outs', c') \<in> set procs`
        `cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
      have "length es = length ins" by fastforce
      from `(px, insx, outsx, cx) \<in> set procs`
        `cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'`
      have "ParamUses wfp (px,Label l) = map fv es"
        by(fastforce intro:ParamUses_Proc_Return_target simp:set_conv_nth)
      with `(px, Label l) = sourcenode a` `length es = length ins`
      show ?case by simp
    qed auto
  next
    fix a assume "valid_edge wfp a"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    thus "distinct (ParamDefs wfp (targetnode a))"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (Main n n')
      from `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `(Main, n') = targetnode a`
      have "ParamDefs wfp (Main,n') = []" by(fastforce intro:ParamDefs_Main_IEdge_Nil)
      with `(Main, n') = targetnode a` show ?case by simp
    next
      case (Proc p ins outs c n n')
      from `(p, ins, outs, c) \<in> set procs` `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'`
      have "ParamDefs wfp (p,n') = []" by(fastforce intro:ParamDefs_Proc_IEdge_Nil)
      with `(p, n') = targetnode a` show ?case by simp
    next
      case (MainCall l p es rets n' ins outs c)
      with `(p, ins, outs, c) \<in> set procs` wf have [simp]:"p \<noteq> Main"
        by fastforce
      from wf `(p, ins, outs, c) \<in> set procs`
      have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
        by(rule in_procs_THE_in_procs_cmd)
      with `(p, Entry) = targetnode a`[THEN sym] show ?case 
        by(auto simp:ParamDefs_def ParamDefs_proc_def)
    next
      case (ProcCall p ins outs c l p' es' rets' l' ins' outs' c')
      with `(p', ins', outs', c') \<in> set procs` wf 
      have [simp]:"p' \<noteq> Main" by fastforce
      from wf `(p', ins', outs', c') \<in> set procs`
      have "(THE cx. \<exists>insx outsx. (p',insx,outsx,cx) \<in> set procs) = c'"
        by(rule in_procs_THE_in_procs_cmd)
      with `(p', Entry) = targetnode a`[THEN sym] show ?case 
        by(fastforce simp:ParamDefs_def ParamDefs_proc_def)
    next
      case (MainReturn l p es rets l' ins outs c)
      from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'`
      have "containsCall procs prog [] p" by(rule Proc_CFG_Call_containsCall)
      with `wf prog procs` `(p, ins, outs, c) \<in> set procs` 
        `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'`
      have "distinct rets" by fastforce
      from `prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'`
      have "ParamDefs wfp (Main,Label l') = rets"
        by(fastforce intro:ParamDefs_Main_Return_target)
      with `distinct rets` `(Main, Label l') = targetnode a` show ?case
        by(fastforce simp:distinct_map inj_on_def)
    next
      case (ProcReturn p ins outs c l p' es' rets' l' ins' outs' c' ps)
      from `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "containsCall procs c [] p'" by(rule Proc_CFG_Call_containsCall)
      with `containsCall procs prog ps p` `(p, ins, outs, c) \<in> set procs`
      have "containsCall procs prog (ps@[p]) p'" by(rule containsCall_in_proc)
      with `wf prog procs` `(p', ins', outs', c') \<in> set procs`
        `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "distinct rets'" by fastforce
      from `(p, ins, outs, c) \<in> set procs`
        `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "ParamDefs wfp (p,Label l') = rets'"
        by(fastforce intro:ParamDefs_Proc_Return_target simp:set_conv_nth)
      with `distinct rets'` `(p, Label l') = targetnode a` show ?case 
        by(fastforce simp:distinct_map inj_on_def)
    next
      case (MainCallReturn n p es rets n')
      from `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
      have "containsCall procs prog [] p" by(rule Proc_CFG_Call_containsCall)
      with `wf prog procs` obtain ins outs c where "(p, ins, outs, c) \<in> set procs"
        by(simp add:wf_def) blast
      with `wf prog procs` `containsCall procs prog [] p`
        `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
      have "distinct rets" by fastforce
      from `prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'`
      have "ParamDefs wfp (Main,n') = rets"
        by(fastforce intro:ParamDefs_Main_Return_target)
      with `distinct rets` `(Main, n') = targetnode a` show ?case
        by(fastforce simp:distinct_map inj_on_def)
    next
      case (ProcCallReturn p ins outs c n p' es' rets' n' ps)
      from `c \<turnstile> n -CEdge (p', es', rets')\<rightarrow>\<^sub>p n'`
      have "containsCall procs c [] p'" by(rule Proc_CFG_Call_containsCall)
      from `Rep_wf_prog wfp = (prog,procs)` `(p, ins, outs, c) \<in> set procs`
        `containsCall procs prog ps p`
      obtain wfp' where "Rep_wf_prog wfp' = (c,procs)" by(erule wfp_Call)
      hence "wf c procs" by(rule wf_wf_prog)
      with `containsCall procs c [] p'` obtain ins' outs' c'
        where "(p', ins', outs', c') \<in> set procs"
        by(simp add:wf_def) blast
      from `containsCall procs prog ps p` `(p, ins, outs, c) \<in> set procs`
        `containsCall procs c [] p'`
      have "containsCall procs prog (ps@[p]) p'" by(rule containsCall_in_proc)
      with `wf prog procs` `(p', ins', outs', c') \<in> set procs`
        `c \<turnstile> n -CEdge (p', es', rets')\<rightarrow>\<^sub>p n'`
      have "distinct rets'" by fastforce
      from `(p, ins, outs, c) \<in> set procs` `c \<turnstile> n -CEdge (p', es', rets')\<rightarrow>\<^sub>p n'`
      have "ParamDefs wfp (p,n') = rets'"
        by(fastforce intro:ParamDefs_Proc_Return_target)
      with `distinct rets'` `(p, n') = targetnode a` show ?case
        by(fastforce simp:distinct_map inj_on_def)
    qed
  next
    fix a Q' p f' ins outs
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
    thus "length (ParamDefs wfp (targetnode a)) = length outs"
      by(rule ParamDefs_length)
  next
    fix n V assume "CFG.valid_node sourcenode targetnode (valid_edge wfp) n"
      and "V \<in> set (ParamDefs wfp n)"
    thus "V \<in> Def wfp n" by(simp add:Def_def)
  next
    fix a Q r p fs ins outs V
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "(p, ins, outs) \<in> set (lift_procs wfp)" and "V \<in> set ins"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p, ins, outs) \<in> set (lift_procs wfp)` `V \<in> set ins`
    show "V \<in> Def wfp (targetnode a)"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' insx outsx cx)
      with wf have [simp]:"insx = ins" by fastforce
      from wf `(p', insx, outsx, cx) \<in> set procs` 
      have "(THE ins'. \<exists>c' outs'. (p',ins',outs',c') \<in> set procs) = 
        insx" by(rule in_procs_THE_in_procs_ins)
      with `(p', Entry) = targetnode a`[THEN sym] `V \<in> set ins`
        `(p', insx, outsx, cx) \<in> set procs` show ?case by(auto simp:Def_def)
    next
      case (ProcCall px insx outsx cx l p' es rets l' ins' outs' c')
      with wf have [simp]:"ins' = ins" by fastforce
      from wf `(p', ins', outs', c') \<in> set procs` 
      have "(THE insx. \<exists>cx outsx. (p',insx,outsx,cx) \<in> set procs) = 
        ins'" by(rule in_procs_THE_in_procs_ins)
      with `(p', Entry) = targetnode a`[THEN sym] `V \<in> set ins`
        `(p', ins', outs', c') \<in> set procs` show ?case by(auto simp:Def_def)
    qed auto
  next
    fix a Q r p fs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show "Def wfp (sourcenode a) = {}"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' insx outsx cx)
      from `(Main, Label l) = sourcenode a`[THEN sym]
        `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "ParamDefs wfp (sourcenode a) = []"
        by(fastforce intro:ParamDefs_Main_CEdge_Nil)
      with `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
        `(Main, Label l) = sourcenode a`[THEN sym]
      show ?case by(fastforce dest:Proc_CFG_Call_source_empty_lhs simp:Def_def)
    next
      case (ProcCall px insx outsx cx l p' es' rets' l' ins' outs' c')
      from `(px, insx, outsx, cx) \<in> set procs` wf
      have [simp]:"px \<noteq> Main" by fastforce
      from `cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "lhs (label cx l) = {}" by(rule Proc_CFG_Call_source_empty_lhs)
      from wf `(px, insx, outsx, cx) \<in> set procs`
      have THE:"(THE c'. \<exists>ins' outs'. (px,ins',outs',c') \<in> set procs) = cx" 
        by(rule in_procs_THE_in_procs_cmd)
      with `(px, Label l) = sourcenode a`[THEN sym]
        `cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`  wf
      have "ParamDefs wfp (sourcenode a) = []"
        by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
        [of _ _ _ _ _ "Label l"] simp:ParamDefs_def ParamDefs_proc_def)
      with `(px, Label l) = sourcenode a`[THEN sym] `lhs (label cx l) = {}` THE
      show ?case by(auto simp:Def_def)
    qed auto
  next
    fix n V assume "CFG.valid_node sourcenode targetnode (valid_edge wfp) n"
      and "V \<in> \<Union>set (ParamUses wfp n)"
    thus "V \<in> Use wfp n" by(fastforce simp:Use_def)
  next
    fix a Q p f ins outs V
    assume "valid_edge wfp a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      and "(p, ins, outs) \<in> set (lift_procs wfp)" and "V \<in> set outs"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p, ins, outs) \<in> set (lift_procs wfp)` `V \<in> set outs`
    show "V \<in> Use wfp (sourcenode a)"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainReturn l p' es rets l' insx outsx cx)
      with wf have [simp]:"outsx = outs" by fastforce
      from wf `(p', insx, outsx, cx) \<in> set procs` 
      have "(THE outs'. \<exists>c' ins'. (p',ins',outs',c') \<in> set procs) = 
        outsx" by(rule in_procs_THE_in_procs_outs)
      with `(p', Exit) = sourcenode a`[THEN sym] `V \<in> set outs`
        `(p', insx, outsx, cx) \<in> set procs` show ?case by(auto simp:Use_def)
    next
      case (ProcReturn px insx outsx cx l p' es' rets' l' ins' outs' c')
      with wf have [simp]:"outs' = outs" by fastforce
      from wf `(p', ins', outs', c') \<in> set procs` 
      have "(THE outsx. \<exists>cx insx. (p',insx,outsx,cx) \<in> set procs) = 
        outs'" by(rule in_procs_THE_in_procs_outs)
      with `(p', Exit) = sourcenode a`[THEN sym] `V \<in> set outs`
        `(p', ins', outs', c') \<in> set procs` show ?case by(auto simp:Use_def)
    qed auto
  next
    fix a V s
    assume "valid_edge wfp a" and "V \<notin> Def wfp (sourcenode a)"
      and "intra_kind (kind a)" and "CFG.pred (kind a) s"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `V \<notin> Def wfp (sourcenode a)` `intra_kind (kind a)` `CFG.pred (kind a) s`
    show "state_val (CFG.transfer (lift_procs wfp) (kind a) s) V = state_val s V"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (Main n n')
      from `CFG.pred (kind a) s` obtain cf cfs where "s = cf#cfs" by(cases s) auto
      show ?case
      proof(cases n)
        case (Label l)
        with `V \<notin> Def wfp (sourcenode a)` `(Main, n) = sourcenode a`
        have "V \<notin> lhs (label prog l)" by(fastforce simp:Def_def)
        with `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `n = Label l`
        have "state_val (CFG.transfer (lift_procs wfp) (kind a) (cf#cfs)) V = fst cf V"
          by(fastforce intro:Proc_CFG_edge_no_lhs_equal)
        with `s = cf#cfs` show ?thesis by simp
      next
        case Entry
        with `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `s = cf#cfs`
        show ?thesis 
          by(fastforce dest:Proc_CFG_EntryD simp:transfers_simps[of wfp,simplified])
      next
        case Exit
        with `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` have False by fastforce
        thus ?thesis by simp
      qed
    next
      case (Proc p ins outs c n n')
      from `CFG.pred (kind a) s` obtain cf cfs where "s = cf#cfs" by(cases s) auto
      from wf `(p, ins, outs, c) \<in> set procs`
      have THE1:"(THE ins'. \<exists>c' outs'. (p,ins',outs',c') \<in> set procs) = ins"
        by(rule in_procs_THE_in_procs_ins)
      from wf `(p, ins, outs, c) \<in> set procs`
      have THE2:"(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
        by(rule in_procs_THE_in_procs_cmd)
      from wf `(p, ins, outs, c) \<in> set procs`
      have [simp]:"p \<noteq> Main" by fastforce
      show ?case
      proof(cases n)
        case (Label l)
        with `V \<notin> Def wfp (sourcenode a)` `(p, n) = sourcenode a`
          `(p, ins, outs, c) \<in> set procs` wf THE1 THE2
        have "V \<notin> lhs (label c l)" by(fastforce simp:Def_def split:split_if_asm)
        with `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `n = Label l`
        have "state_val (CFG.transfer (lift_procs wfp) (kind a) (cf#cfs)) V = fst cf V"
          by(fastforce intro:Proc_CFG_edge_no_lhs_equal)
        with `s = cf#cfs` show ?thesis by simp
      next
        case Entry
        with `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `s = cf#cfs`
        show ?thesis
          by(fastforce dest:Proc_CFG_EntryD simp:transfers_simps[of wfp,simplified])
      next
        case Exit
        with `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` have False by fastforce
        thus ?thesis by simp
      qed
    next
      case MainCallReturn thus ?case by(cases s,auto simp:intra_kind_def)
    next
      case ProcCallReturn thus ?case by(cases s,auto simp:intra_kind_def)
    qed(auto simp:intra_kind_def)
  next
    fix a s s'
    assume "valid_edge wfp a" 
      and "\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V"
      and "intra_kind (kind a)" and "CFG.pred (kind a) s" and "CFG.pred (kind a) s'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from `CFG.pred (kind a) s` obtain cf cfs where [simp]:"s = cf#cfs" 
      by(cases s) auto
    from `CFG.pred (kind a) s'` obtain cf' cfs' where [simp]:"s' = cf'#cfs'" 
      by(cases s') auto
    from `prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a` `intra_kind (kind a)`
      `\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V`
      `CFG.pred (kind a) s` `CFG.pred (kind a) s'`
    show "\<forall>V\<in>Def wfp (sourcenode a). 
      state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
      state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (Main n n')
      show ?case
      proof(cases n)
        case (Label l)
        with `\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V`
          `(Main, n) = sourcenode a`[THEN sym]
        have rhs:"\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V"
          and PDef:"\<forall>V\<in>set (ParamDefs wfp (sourcenode a)). 
          state_val s V = state_val s' V"
          by(auto simp:Use_def)
        from rhs `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `n = Label l` `CFG.pred (kind a) s` 
          `CFG.pred (kind a) s'`
        have lhs:"\<forall>V\<in>lhs (label prog l). 
          state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by -(rule Proc_CFG_edge_uses_only_rhs,auto)
        from PDef `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `(Main, n) = sourcenode a`[THEN sym]
        have "\<forall>V\<in>set (ParamDefs wfp (sourcenode a)). 
          state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by(fastforce dest:Proc_CFG_Call_follows_id_edge 
            simp:ParamDefs_def ParamDefs_proc_def transfers_simps[of wfp,simplified]
            split:split_if_asm)
        with lhs `(Main, n) = sourcenode a`[THEN sym] Label show ?thesis
          by(fastforce simp:Def_def)
      next
        case Entry
        with `(Main, n) = sourcenode a`[THEN sym]
        show ?thesis by(fastforce simp:Entry_Def_empty)
      next
        case Exit
        with `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` have False by fastforce
        thus ?thesis by simp
      qed
    next
      case (Proc p ins outs c n n')
      show ?case
      proof(cases n)
        case (Label l)
        with `\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V` wf
          `(p, n) = sourcenode a`[THEN sym] `(p, ins, outs, c) \<in> set procs`
        have rhs:"\<forall>V\<in>rhs (label c l). state_val s V = state_val s' V"
          and PDef:"\<forall>V\<in>set (ParamDefs wfp (sourcenode a)). 
          state_val s V = state_val s' V"
          by(auto dest:in_procs_THE_in_procs_cmd simp:Use_def split:split_if_asm)
        from rhs `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `n = Label l` `CFG.pred (kind a) s` 
          `CFG.pred (kind a) s'`
        have lhs:"\<forall>V\<in>lhs (label c l). 
          state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by -(rule Proc_CFG_edge_uses_only_rhs,auto)
        from `(p, ins, outs, c) \<in> set procs` wf have [simp]:"p \<noteq> Main" by fastforce
        from wf `(p, ins, outs, c) \<in> set procs`
        have THE:"(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c" 
          by(fastforce intro:in_procs_THE_in_procs_cmd)
        with PDef `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `(p, n) = sourcenode a`[THEN sym]
        have "\<forall>V\<in>set (ParamDefs wfp (sourcenode a)). 
          state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by(fastforce dest:Proc_CFG_Call_follows_id_edge 
            simp:ParamDefs_def ParamDefs_proc_def transfers_simps[of wfp,simplified]
            split:split_if_asm)
        with lhs `(p, n) = sourcenode a`[THEN sym] Label THE
        show ?thesis by(auto simp:Def_def)
      next
        case Entry
        with wf `(p, ins, outs, c) \<in> set procs` have "ParamDefs wfp (p,n) = []"
          by(fastforce simp:ParamDefs_def ParamDefs_proc_def)
        moreover
        from Entry `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `(p, ins, outs, c) \<in> set procs`
        have "ParamUses wfp (p,n) = []" by(fastforce intro:ParamUses_Proc_IEdge_Nil)
        ultimately have "\<forall>V\<in>set ins. state_val s V = state_val s' V"
          using wf `(p, ins, outs, c) \<in> set procs` `(p,n) = sourcenode a`
          `\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V`  Entry
          by(fastforce dest:in_procs_THE_in_procs_ins simp:Use_def split:split_if_asm)
        with `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` Entry
        have "\<forall>V\<in>set ins. state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by(fastforce dest:Proc_CFG_EntryD simp:transfers_simps[of wfp,simplified])
        with `(p,n) = sourcenode a`[THEN sym] Entry wf  
          `(p, ins, outs, c) \<in> set procs` `ParamDefs wfp (p,n) = []`
        show ?thesis by(auto dest:in_procs_THE_in_procs_ins simp:Def_def)
      next
        case Exit
        with `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` have False by fastforce
        thus ?thesis by simp
      qed
    qed(auto simp:intra_kind_def)
  next
    fix a s fix s'::"((char list \<rightharpoonup> val) \<times> node) list"
    assume "valid_edge wfp a" and "CFG.pred (kind a) s"
      and "\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V" 
      and "length s = length s'" and "snd (hd s) = snd (hd s')"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from `CFG.pred (kind a) s` obtain cf cfs where [simp]:"s = cf#cfs" 
      by(cases s) auto
    from `length s = length s'` obtain cf' cfs' where [simp]:"s' = cf'#cfs'" 
      by(cases s') auto
    from `prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a` `CFG.pred (kind a) s`
      `\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V`
      `length s = length s'` `snd (hd s) = snd (hd s')`
    show "CFG.pred (kind a) s'"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (Main n n')
      show ?case
      proof(cases n)
        case (Label l)
        with `\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V`
          `(Main, n) = sourcenode a`
        have "\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V" 
          by(fastforce simp:Use_def)
        with `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` Label `CFG.pred (kind a) s`
          `length s = length s'`
        show ?thesis by(fastforce intro:Proc_CFG_edge_rhs_pred_eq)
      next
        case Entry
        with `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `CFG.pred (kind a) s`
        show ?thesis by(fastforce dest:Proc_CFG_EntryD)
      next
        case Exit
        with `prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` have False by fastforce
        thus ?thesis by simp
      qed
    next
      case (Proc p ins outs c n n')
      show ?case
      proof(cases n)
        case (Label l)
        with `\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V` wf
          `(p, n) = sourcenode a`[THEN sym] `(p, ins, outs, c) \<in> set procs`
        have "\<forall>V\<in>rhs (label c l). state_val s V = state_val s' V"
          by(auto dest:in_procs_THE_in_procs_cmd simp:Use_def split:split_if_asm)
        with `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` Label `CFG.pred (kind a) s`
          `length s = length s'`
        show ?thesis by(fastforce intro:Proc_CFG_edge_rhs_pred_eq)
      next
        case Entry
        with `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` `CFG.pred (kind a) s`
        show ?thesis by(fastforce dest:Proc_CFG_EntryD)
      next
        case Exit
        with `c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'` have False by fastforce
        thus ?thesis by simp
      qed
    next
      case (MainReturn l p es rets l' ins outs c)
      with `\<lambda>cf. snd cf = (Main, Label l')\<hookleftarrow>\<^bsub>p\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs) =
        kind a`[THEN sym]
      show ?case by fastforce
    next
      case (ProcReturn p ins outs c l p' es rets l' ins' outs' c')
      with `\<lambda>cf. snd cf = (p, Label l')\<hookleftarrow>\<^bsub>p'\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs') =
        kind a`[THEN sym]
      show ?case by fastforce
    qed(auto dest:sym)
  next
    fix a Q r p fs ins outs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p, ins, outs) \<in> set (lift_procs wfp)`
    show "length fs = length ins"
    proof(induct rule:PCFG.induct)
      case (MainCall l p' es rets n' ins' outs' c)
      hence "fs = map interpret es" and "p' = p" by simp_all
      with wf `(p, ins, outs) \<in> set (lift_procs wfp)`
        `(p', ins', outs', c) \<in> set procs`
      have [simp]:"ins' = ins" by fastforce
      from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "containsCall procs prog [] p'" by(rule Proc_CFG_Call_containsCall)
      with `wf prog procs` `(p', ins', outs', c) \<in> set procs`
        `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "length es = length ins" by fastforce
      with `fs = map interpret es` show ?case by simp
    next
      case (ProcCall px insx outsx c l p' es' rets' l' ins' outs' c' ps)
      hence "fs = map interpret es'" and "p' = p" by simp_all
      with wf `(p, ins, outs) \<in> set (lift_procs wfp)`
        `(p', ins', outs', c') \<in> set procs`
      have [simp]:"ins' = ins" by fastforce
      from `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "containsCall procs c [] p'" by(rule Proc_CFG_Call_containsCall)
      with `containsCall procs prog ps px` `(px, insx, outsx, c) \<in> set procs`
      have "containsCall procs prog (ps@[px]) p'" by(rule containsCall_in_proc)
      with `wf prog procs` `(p', ins', outs', c') \<in> set procs`
        `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "length es' = length ins" by fastforce
      with `fs = map interpret es'` show ?case by simp
    qed auto
  next
    fix a Q r p fs a' Q' r' p' fs' s s'
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "valid_edge wfp a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'" 
      and "sourcenode a = sourcenode a'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      and "prog,procs \<turnstile> sourcenode a' -kind a'\<rightarrow> targetnode a'"
      by(simp_all add:valid_edge_def)
    from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'` show "a = a'"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainCall l px es rets n' insx outsx cx)
      from `prog,procs \<turnstile> sourcenode a' -kind a'\<rightarrow> targetnode a'`
        `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'` 
        `(Main, Label l) = sourcenode a` `sourcenode a = sourcenode a'`
        `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p n'` wf
      have "targetnode a' = (px, Entry)"
        by(fastforce elim!:PCFG.cases dest:Proc_CFG_Call_nodes_eq)
      with `valid_edge wfp a` `valid_edge wfp a'`
        `sourcenode a = sourcenode a'` `(px, Entry) = targetnode a` wf
      have "kind a = kind a'" by(fastforce intro:Proc_CFG_edge_det simp:valid_edge_def)
      with `sourcenode a = sourcenode a'` `(px, Entry) = targetnode a`
        `targetnode a' = (px, Entry)`
      show ?case by(cases a,cases a',auto)
    next
      case (ProcCall px ins outs c l px' es rets l' insx outsx cx)
      with wf have "px \<noteq> Main" by fastforce
      with `prog,procs \<turnstile> sourcenode a' -kind a'\<rightarrow> targetnode a'`
        `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'`
        `(px, Label l) = sourcenode a` `sourcenode a = sourcenode a'`
        `c \<turnstile> Label l -CEdge (px', es, rets)\<rightarrow>\<^sub>p Label l'`
        `(px', insx, outsx, cx) \<in> set procs` `(px, ins, outs, c) \<in> set procs`
      have "targetnode a' = (px', Entry)"
      proof(induct n\<equiv>"sourcenode a'" et\<equiv>"kind a'" n'\<equiv>"targetnode a'" rule:PCFG.induct)
        case (ProcCall p insa outsa ca la p'a es' rets' l'a ins' outs' c')
        hence [simp]:"px = p" "l = la" by(auto dest:sym)
        from `(p, insa, outsa, ca) \<in> set procs`
          `(px, ins, outs, c) \<in> set procs` wf have [simp]:"ca = c"  by auto
        from `ca \<turnstile> Label la -CEdge (p'a, es', rets')\<rightarrow>\<^sub>p Label l'a`
          `c \<turnstile> Label l -CEdge (px', es, rets)\<rightarrow>\<^sub>p Label l'`
        have "p'a = px'" by(fastforce dest:Proc_CFG_Call_nodes_eq)
        with `(p'a, Entry) = targetnode a'` show ?case by simp
      qed(auto dest:sym)
      with `valid_edge wfp a` `valid_edge wfp a'`
        `sourcenode a = sourcenode a'` `(px', Entry) = targetnode a` wf
      have "kind a = kind a'" by(fastforce intro:Proc_CFG_edge_det simp:valid_edge_def)
      with `sourcenode a = sourcenode a'` `(px', Entry) = targetnode a`
        `targetnode a' = (px', Entry)` show ?case by(cases a,cases a',auto)
    qed auto
  next
    fix a Q r p fs i ins outs fix s s'::"((char list \<rightharpoonup> val) \<times> node) list"
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "i < length ins"
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
      and "\<forall>V\<in>ParamUses wfp (sourcenode a) ! i. state_val s V = state_val s' V"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `i < length ins` 
      `(p, ins, outs) \<in> set (lift_procs wfp)` 
      `\<forall>V\<in>ParamUses wfp (sourcenode a) ! i. state_val s V = state_val s' V`
    show "CFG.params fs (state_val s) ! i = CFG.params fs (state_val s') ! i"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' insx outsx cx)
      with wf have [simp]:"insx = ins" "fs = map interpret es" by auto
      from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "containsCall procs prog [] p'" by(rule Proc_CFG_Call_containsCall)
      with `wf prog procs` `(p', insx, outsx, cx) \<in> set procs` 
        `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "length es = length ins" by fastforce
      with `i < length ins` have "i < length (map interpret es)" by simp
      from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'`
      have "ParamUses wfp (Main,Label l) = map fv es"
        by(fastforce intro:ParamUses_Main_Return_target)
      with `\<forall>V\<in>ParamUses wfp (sourcenode a) ! i. state_val s V = state_val s' V`
        `i < length (map interpret es)` `(Main, Label l) = sourcenode a`
      have " ((map (\<lambda>e cf. interpret e cf) es)!i) (fst (hd s)) = 
        ((map (\<lambda>e cf. interpret e cf) es)!i) (fst (hd s'))"
        by(cases "interpret (es ! i) (fst (hd s))")(auto dest:rhs_interpret_eq)
      with `i < length (map interpret es)` show ?case by(simp add:ProcCFG.params_nth)
    next
      case (ProcCall px insx outsx cx l p' es' rets' l' ins' outs' c' ps)
      with wf have [simp]:"ins' = ins" by fastforce
      from `cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "containsCall procs cx [] p'" by(rule Proc_CFG_Call_containsCall)
      with `containsCall procs prog ps px` `(px, insx, outsx, cx) \<in> set procs`
      have "containsCall procs prog (ps@[px]) p'" by(rule containsCall_in_proc)
      with `wf prog procs` `(p', ins', outs', c') \<in> set procs`
        `cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "length es' = length ins" by fastforce
      from `\<lambda>s. True:(px, Label l')\<hookrightarrow>\<^bsub>p'\<^esub>map interpret es' = kind a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "fs = map interpret es'" by simp_all
      from `i < length ins` `fs = map interpret es'` 
        `length es' = length ins` have "i < length fs" by simp
      from `(px, insx, outsx, cx) \<in> set procs`
        `cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'`
      have "ParamUses wfp (px,Label l) = map fv es'"
        by(auto intro!:ParamUses_Proc_Return_target simp:set_conv_nth)
      with `\<forall>V\<in>ParamUses wfp (sourcenode a) ! i. state_val s V = state_val s' V`
        `(px, Label l) = sourcenode a` `i < length fs` 
        `fs = map interpret es'`
      have " ((map (\<lambda>e cf. interpret e cf) es')!i) (fst (hd s)) = 
        ((map (\<lambda>e cf. interpret e cf) es')!i) (fst (hd s'))"
        by(cases "interpret (es' ! i) (fst (hd s))")(auto dest:rhs_interpret_eq)
      with `i < length fs` `fs = map interpret es'` 
      show ?case by(simp add:ProcCFG.params_nth)
    qed auto
  next
    fix a Q' p f' ins outs cf cf'
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
    thus "f' cf cf' = cf'(ParamDefs wfp (targetnode a) [:=] map cf outs)"
      by(rule Return_update)
  next
    fix a a'
    assume "valid_edge wfp a" and "valid_edge wfp a'"
      and "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'"
      and "intra_kind (kind a)" and "intra_kind (kind a')"
    with wf show "\<exists>Q Q'. kind a = (Q)\<^sub>\<surd> \<and> kind a' = (Q')\<^sub>\<surd> \<and> 
      (\<forall>cf. (Q cf \<longrightarrow> \<not> Q' cf) \<and> (Q' cf \<longrightarrow> \<not> Q cf))"
      by(auto dest:Proc_CFG_deterministic simp:valid_edge_def)
  qed
qed


subsection {* Instantiating the @{text CFGExit_wf} locale *}

interpretation ProcCFGExit_wf:
  CFGExit_wf sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main "(Main,Exit)"
  "Def wfp" "Use wfp" "ParamDefs wfp" "ParamUses wfp"
  for wfp
proof
  from Exit_Def_empty Exit_Use_empty
  show "Def wfp (Main, Exit) = {} \<and> Use wfp (Main, Exit) = {}" by simp
qed


end