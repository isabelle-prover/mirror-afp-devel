section {* Equivalence *}

theory WEquivalence imports Semantics WCFG begin


subsection {* From @{term "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"} to\\
  @{term "c \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)"} with @{term transfers} and @{term preds} *}

lemma Skip_WCFG_edge_Exit:
  "\<lbrakk>labels prog l Skip\<rbrakk> \<Longrightarrow> prog \<turnstile> (_ l _) -\<Up>id\<rightarrow> (_Exit_)"
proof(induct prog l Skip rule:labels.induct)
  case Labels_Base
  show ?case by(fastforce intro:WCFG_Skip)
next
  case (Labels_LAss V e)
  show ?case by(rule WCFG_LAssSkip)
next
  case (Labels_Seq2 c\<^sub>2 l c\<^sub>1)
  from `c\<^sub>2 \<turnstile> (_ l _) -\<Up>id\<rightarrow> (_Exit_)`
  have "c\<^sub>1;;c\<^sub>2 \<turnstile> (_ l _) \<oplus> #:c\<^sub>1 -\<Up>id\<rightarrow> (_Exit_) \<oplus> #:c\<^sub>1"
    by(fastforce intro:WCFG_SeqSecond)
  thus ?case by(simp del:id_apply)
next
  case (Labels_CondTrue c\<^sub>1 l b c\<^sub>2)
  from `c\<^sub>1 \<turnstile> (_ l _) -\<Up>id\<rightarrow> (_Exit_)`
  have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> (_ l _) \<oplus> 1 -\<Up>id\<rightarrow> (_Exit_) \<oplus> 1"
    by(fastforce intro:WCFG_CondThen)
  thus ?case by(simp del:id_apply)
next
  case (Labels_CondFalse c\<^sub>2 l b c\<^sub>1)
  from `c\<^sub>2 \<turnstile> (_ l _) -\<Up>id\<rightarrow> (_Exit_)`
  have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> (_ l _) \<oplus> (#:c\<^sub>1 + 1) -\<Up>id\<rightarrow> (_Exit_) \<oplus> (#:c\<^sub>1 + 1)"
    by(fastforce intro:WCFG_CondElse)
  thus ?case by(simp del:id_apply)
next
  case (Labels_WhileExit b c')
  show ?case by(rule WCFG_WhileFalseSkip)
qed


lemma step_WCFG_edge:
  assumes "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
  obtains et where "prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)" and "transfer et s = s'"
  and "pred et s"
proof -
  from `prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>`
  have "\<exists>et. prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _) \<and> transfer et s = s' \<and> pred et s"
  proof(induct rule:step.induct)
    case (StepLAss V e s)
    have "pred \<Up>(\<lambda>s. s(V:=(interpret e s))) s" by simp
    have "V:=e \<turnstile> (_0_) -\<Up>(\<lambda>s. s(V:=(interpret e s)))\<rightarrow> (_1_)"
      by(rule WCFG_LAss)
    have "transfer \<Up>(\<lambda>s. s(V:=(interpret e s))) s = s(V:=(interpret e s))" by simp
    with `pred \<Up>(\<lambda>s. s(V:=(interpret e s))) s`
      `V:=e \<turnstile> (_0_) -\<Up>(\<lambda>s. s(V:=(interpret e s)))\<rightarrow> (_1_)` show ?case by blast
  next
    case (StepSeq c\<^sub>1 c\<^sub>2 l s)
    from `labels (c\<^sub>1;;c\<^sub>2) l (Skip;;c\<^sub>2)` `l < #:c\<^sub>1` have "labels c\<^sub>1 l Skip"
      by(auto elim:labels.cases intro:Labels_Base)
    hence "c\<^sub>1 \<turnstile> (_ l _) -\<Up>id\<rightarrow> (_Exit_)" 
      by(fastforce intro:Skip_WCFG_edge_Exit)
    hence "c\<^sub>1;;c\<^sub>2 \<turnstile> (_ l _) -\<Up>id\<rightarrow> (_0_) \<oplus> #:c\<^sub>1" 
      by(rule WCFG_SeqConnect,simp)
    thus ?case by auto
  next
    case (StepSeqWhile b cx l s)
    from `labels (while (b) cx) l (Skip;;while (b) cx)`
    obtain lx where "labels cx lx Skip" 
      and [simp]:"l = lx + 2" by(auto elim:labels.cases)
    hence "cx \<turnstile> (_ lx _) -\<Up>id\<rightarrow> (_Exit_)" 
      by(fastforce intro:Skip_WCFG_edge_Exit)
    hence "while (b) cx \<turnstile> (_ lx _) \<oplus> 2 -\<Up>id\<rightarrow> (_0_)"
      by(fastforce intro:WCFG_WhileBodyExit)
    thus ?case by auto
  next
    case (StepCondTrue b s c\<^sub>1 c\<^sub>2)
    from `interpret b s = Some true`
    have "pred (\<lambda>s. interpret b s = Some true)\<^sub>\<surd> s" by simp
    moreover
    have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some true)\<^sub>\<surd>\<rightarrow> (_0_) \<oplus> 1"
      by(rule WCFG_CondTrue)
    moreover
    have "transfer (\<lambda>s. interpret b s = Some true)\<^sub>\<surd> s = s" by simp
    ultimately show ?case by auto
  next
    case (StepCondFalse b s c\<^sub>1 c\<^sub>2)
    from `interpret b s = Some false`
    have "pred (\<lambda>s. interpret b s = Some false)\<^sub>\<surd> s" by simp
    moreover
    have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some false)\<^sub>\<surd>\<rightarrow> 
                                   (_0_) \<oplus> (#:c\<^sub>1 + 1)"
      by(rule WCFG_CondFalse)
    moreover
    have "transfer (\<lambda>s. interpret b s = Some false)\<^sub>\<surd> s = s" by simp
    ultimately show ?case by auto
  next
    case (StepWhileTrue b s c)
    from `interpret b s = Some true`
    have "pred (\<lambda>s. interpret b s = Some true)\<^sub>\<surd> s" by simp
    moreover
    have "while (b) c \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some true)\<^sub>\<surd>\<rightarrow> (_0_) \<oplus> 2" 
      by(rule WCFG_WhileTrue)
    moreover
    have "transfer (\<lambda>s. interpret b s = Some true)\<^sub>\<surd> s = s" by simp
    ultimately show ?case by(auto simp del:add_2_eq_Suc')
  next
    case (StepWhileFalse b s c)
    from `interpret b s = Some false`
    have "pred (\<lambda>s. interpret b s = Some false)\<^sub>\<surd> s" by simp
    moreover
    have "while (b) c \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some false)\<^sub>\<surd>\<rightarrow> (_1_)"
      by(rule WCFG_WhileFalse)
    moreover
    have "transfer (\<lambda>s. interpret b s = Some false)\<^sub>\<surd> s = s" by simp
    ultimately show ?case by auto
  next
    case (StepRecSeq1 prog c s l c' s' l' c\<^sub>2)
    from `\<exists>et. prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _) \<and> transfer et s = s' \<and> pred et s`
    obtain et where "prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)" 
      and "transfer et s = s'" and "pred et s" by blast
    moreover
    from `prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)` have "prog;;c\<^sub>2 \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)"
      by(fastforce intro:WCFG_SeqFirst)
    ultimately show ?case by blast
  next
    case (StepRecSeq2 prog c s l c' s' l' c\<^sub>1)
    from `\<exists>et. prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _) \<and> transfer et s = s' \<and> pred et s`
    obtain et where "prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)" 
      and "transfer et s = s'" and "pred et s" by blast
    moreover
    from `prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)` 
    have "c\<^sub>1;;prog \<turnstile> (_ l _) \<oplus> #:c\<^sub>1 -et\<rightarrow> (_ l' _) \<oplus> #:c\<^sub>1"
      by(fastforce intro:WCFG_SeqSecond)
    ultimately show ?case by simp blast
  next
    case (StepRecCond1 prog c s l c' s' l' b c\<^sub>2)
    from `\<exists>et. prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _) \<and> transfer et s = s' \<and> pred et s`
    obtain et where "prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)" 
      and "transfer et s = s'" and "pred et s" by blast
    moreover
    from `prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)` 
    have "if (b) prog else c\<^sub>2 \<turnstile> (_ l _) \<oplus> 1 -et\<rightarrow> (_ l' _) \<oplus> 1"
      by(fastforce intro:WCFG_CondThen)
    ultimately show ?case by simp blast
  next
    case (StepRecCond2 prog c s l c' s' l' b c\<^sub>1)
    from `\<exists>et. prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _) \<and> transfer et s = s' \<and> pred et s`
    obtain et where "prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)" 
      and "transfer et s = s'" and "pred et s" by blast
    moreover
    from `prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)`
    have "if (b) c\<^sub>1 else prog \<turnstile> (_ l _) \<oplus> (#:c\<^sub>1 + 1) -et\<rightarrow> (_ l' _) \<oplus> (#:c\<^sub>1 + 1)"
      by(fastforce intro:WCFG_CondElse)
    ultimately show ?case by simp blast
  next
    case (StepRecWhile cx c s l c' s' l' b)
    from `\<exists>et. cx \<turnstile> (_ l _) -et\<rightarrow> (_ l' _) \<and> transfer et s = s' \<and> pred et s`
    obtain et where "cx \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)"
      and "transfer et s = s'" and "pred et s" by blast
    moreover
    hence "while (b) cx \<turnstile> (_ l _) \<oplus> 2 -et\<rightarrow> (_ l' _) \<oplus> 2"
      by(fastforce intro:WCFG_WhileBody)
    ultimately show ?case by simp blast
  qed
  with that show ?thesis by blast
qed


subsection {* From @{term "c \<turnstile> (_ l _) -et\<rightarrow> (_ l' _)"} with @{term transfers} 
  and @{term preds} to\\
  @{term "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"} *}

(*<*)declare One_nat_def [simp del] add_2_eq_Suc' [simp del](*>*)

lemma WCFG_edge_Exit_Skip:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow> (_Exit_); n \<noteq> (_Entry_)\<rbrakk>
  \<Longrightarrow> \<exists>l. n = (_ l _) \<and> labels prog l Skip \<and> et = \<Up>id"
proof(induct prog n et "(_Exit_)" rule:WCFG_induct)
  case WCFG_Skip show ?case by(fastforce intro:Labels_Base)
next
  case WCFG_LAssSkip show ?case by(fastforce intro:Labels_LAss)
next
  case (WCFG_SeqSecond c\<^sub>2 n et n' c\<^sub>1)
  note IH = `\<lbrakk>n' = (_Exit_); n \<noteq> (_Entry_)\<rbrakk> 
    \<Longrightarrow> \<exists>l. n = (_ l _) \<and> labels c\<^sub>2 l Skip \<and> et = \<Up>id`
  from `n' \<oplus> #:c\<^sub>1 = (_Exit_)` have "n' = (_Exit_)" by(cases n') auto
  from IH[OF this `n \<noteq> (_Entry_)`] obtain l where [simp]:"n = (_ l _)" "et = \<Up>id"
    and "labels c\<^sub>2 l Skip" by blast
  hence "labels (c\<^sub>1;;c\<^sub>2) (l + #:c\<^sub>1) Skip" by(fastforce intro:Labels_Seq2)
  thus ?case by(fastforce simp:id_def)
next
  case (WCFG_CondThen c\<^sub>1 n et n' b c\<^sub>2)
  note IH = `\<lbrakk>n' = (_Exit_); n \<noteq> (_Entry_)\<rbrakk>
    \<Longrightarrow> \<exists>l. n = (_ l _) \<and> labels c\<^sub>1 l Skip \<and> et = \<Up>id`
  from `n' \<oplus> 1 = (_Exit_)` have "n' = (_Exit_)" by(cases n') auto
  from IH[OF this `n \<noteq> (_Entry_)`] obtain l where [simp]:"n = (_ l _)" "et = \<Up>id"
    and "labels c\<^sub>1 l Skip" by blast
  hence "labels (if (b) c\<^sub>1 else c\<^sub>2) (l + 1) Skip"
    by(fastforce intro:Labels_CondTrue)
  thus ?case by(fastforce simp:id_def)
next
  case (WCFG_CondElse c\<^sub>2 n et n' b c\<^sub>1)
  note IH = `\<lbrakk>n' = (_Exit_); n \<noteq> (_Entry_)\<rbrakk>
    \<Longrightarrow> \<exists>l. n = (_ l _) \<and> labels c\<^sub>2 l Skip \<and> et = \<Up>id`
  from `n' \<oplus> #:c\<^sub>1 + 1 = (_Exit_)` have "n' = (_Exit_)" by(cases n') auto
  from IH[OF this `n \<noteq> (_Entry_)`] obtain l where [simp]:"n = (_ l _)" "et = \<Up>id"
    and label:"labels c\<^sub>2 l Skip" by blast
  hence "labels (if (b) c\<^sub>1 else c\<^sub>2) (l + #:c\<^sub>1 + 1) Skip"
    by(fastforce intro:Labels_CondFalse)
  thus ?case by(fastforce simp:add.assoc id_def)
next
  case WCFG_WhileFalseSkip show ?case by(fastforce intro:Labels_WhileExit)
next
  case (WCFG_WhileBody c' n et n' b) thus ?case by(cases n') auto
qed simp_all


lemma WCFG_edge_step:
  "\<lbrakk>prog \<turnstile> (_ l _) -et\<rightarrow> (_ l' _); transfer et s = s'; pred et s\<rbrakk>
  \<Longrightarrow> \<exists>c c'. prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels prog l c \<and> labels prog l' c'"
proof(induct prog "(_ l _)" et "(_ l' _)" arbitrary:l l' rule:WCFG_induct)
  case (WCFG_LAss V e)
  from `transfer \<Up>\<lambda>s. s(V:=(interpret e s)) s = s'`
  have [simp]:"s' = s(V:=(interpret e s))" by(simp del:fun_upd_apply)
  have "labels (V:=e) 0 (V:=e)" by(fastforce intro:Labels_Base)
  moreover
  hence "labels (V:=e) 1 Skip" by(fastforce intro:Labels_LAss)
  ultimately show ?case
    apply(rule_tac x="V:=e" in exI)
    apply(rule_tac x="Skip" in exI)
    by(fastforce intro:StepLAss simp del:fun_upd_apply)
next
  case (WCFG_SeqFirst c\<^sub>1 et c\<^sub>2)
  note IH = `\<lbrakk>transfer et s = s'; pred et s\<rbrakk>
    \<Longrightarrow> \<exists>c c'. c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels c\<^sub>1 l c \<and> labels c\<^sub>1 l' c'`
  from IH[OF `transfer et s = s'` `pred et s`]
  obtain c c' where "c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
    and "labels c\<^sub>1 l c" and "labels c\<^sub>1 l' c'" by blast
  from `c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>` have "c\<^sub>1;;c\<^sub>2 \<turnstile> \<langle>c;;c\<^sub>2,s,l\<rangle> \<leadsto> \<langle>c';;c\<^sub>2,s',l'\<rangle>"
    by(rule StepRecSeq1)
  moreover 
  from `labels c\<^sub>1 l c` have "labels (c\<^sub>1;;c\<^sub>2) l (c;;c\<^sub>2)"
    by(fastforce intro:Labels_Seq1)
  moreover 
  from `labels c\<^sub>1 l' c'` have "labels (c\<^sub>1;;c\<^sub>2) l' (c';;c\<^sub>2)"
    by(fastforce intro:Labels_Seq1)
  ultimately show ?case by blast
next
  case (WCFG_SeqConnect c\<^sub>1 et c\<^sub>2)
  from `c\<^sub>1 \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)`
  have "labels c\<^sub>1 l Skip" and [simp]:"et = \<Up>id"
    by(auto dest:WCFG_edge_Exit_Skip)
  from `transfer et s = s'` have [simp]:"s' = s" by simp
  have "labels c\<^sub>2 0 c\<^sub>2" by(fastforce intro:Labels_Base)
  hence "labels (c\<^sub>1;;c\<^sub>2) #:c\<^sub>1 c\<^sub>2" by(fastforce dest:Labels_Seq2)
  moreover
  from `labels c\<^sub>1 l Skip` have "labels (c\<^sub>1;;c\<^sub>2) l (Skip;;c\<^sub>2)"
    by(fastforce intro:Labels_Seq1)
  moreover
  from `labels c\<^sub>1 l Skip` have "l < #:c\<^sub>1" by(rule label_less_num_inner_nodes)
  ultimately 
  have "c\<^sub>1;;c\<^sub>2 \<turnstile> \<langle>Skip;;c\<^sub>2,s,l\<rangle> \<leadsto> \<langle>c\<^sub>2,s,#:c\<^sub>1\<rangle>" by -(rule StepSeq)
  with `labels (c\<^sub>1;;c\<^sub>2) l (Skip;;c\<^sub>2)`
    `labels (c\<^sub>1;;c\<^sub>2) #:c\<^sub>1 c\<^sub>2` `(_0_) \<oplus> #:c\<^sub>1 = (_ l' _)` show ?case by simp blast
next
  case (WCFG_SeqSecond c\<^sub>2 n et n' c\<^sub>1)
  note IH = `\<And>l l'. \<lbrakk>n = (_ l _); n' = (_ l' _); transfer et s = s'; pred et s\<rbrakk>
    \<Longrightarrow> \<exists>c c'. c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels c\<^sub>2 l c \<and> labels c\<^sub>2 l' c'`
  from `n \<oplus> #:c\<^sub>1 = (_ l _)` obtain lx where "n = (_ lx _)" 
    and [simp]:"l = lx + #:c\<^sub>1"
    by(cases n) auto
  from `n' \<oplus> #:c\<^sub>1 = (_ l' _)` obtain lx' where "n' = (_ lx' _)" 
    and [simp]:"l' = lx' + #:c\<^sub>1"
    by(cases n') auto
  from IH[OF `n = (_ lx _)` `n' = (_ lx' _)` `transfer et s = s'` `pred et s`]
  obtain c c' where "c\<^sub>2 \<turnstile> \<langle>c,s,lx\<rangle> \<leadsto> \<langle>c',s',lx'\<rangle>"
    and "labels c\<^sub>2 lx c" and "labels c\<^sub>2 lx' c'" by blast
  from `c\<^sub>2 \<turnstile> \<langle>c,s,lx\<rangle> \<leadsto> \<langle>c',s',lx'\<rangle>` have "c\<^sub>1;;c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
    by(fastforce intro:StepRecSeq2)
  moreover 
  from `labels c\<^sub>2 lx c` have "labels (c\<^sub>1;;c\<^sub>2) l c" by(fastforce intro:Labels_Seq2)
  moreover 
  from `labels c\<^sub>2 lx' c'` have "labels (c\<^sub>1;;c\<^sub>2) l' c'" by(fastforce intro:Labels_Seq2)
  ultimately show ?case by blast
next
  case (WCFG_CondTrue b c\<^sub>1 c\<^sub>2)
  from `(_0_) \<oplus> 1 = (_ l' _)` have [simp]:"l' = 1" by simp
  from `transfer (\<lambda>s. interpret b s = Some true)\<^sub>\<surd> s = s'` have [simp]:"s' = s" by simp
  have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)"
    by(fastforce intro:Labels_Base)
  have "labels c\<^sub>1 0 c\<^sub>1" by(fastforce intro:Labels_Base)
  hence "labels (if (b) c\<^sub>1 else c\<^sub>2) 1 c\<^sub>1" by(fastforce dest:Labels_CondTrue)
  from `pred (\<lambda>s. interpret b s = Some true)\<^sub>\<surd> s`
  have "interpret b s = Some true" by simp
  hence "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>1,s,1\<rangle>"
    by(rule StepCondTrue)
  with  `labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)`
    `labels (if (b) c\<^sub>1 else c\<^sub>2) 1 c\<^sub>1` show ?case by simp blast
next
  case (WCFG_CondFalse b c\<^sub>1 c\<^sub>2)
  from `(_0_) \<oplus> #:c\<^sub>1 + 1 = (_ l' _)` have [simp]:"l' = #:c\<^sub>1 + 1" by simp
  from `transfer (\<lambda>s. interpret b s = Some false)\<^sub>\<surd> s = s'` have [simp]:"s' = s"
    by simp
  have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)"
    by(fastforce intro:Labels_Base)
  have "labels c\<^sub>2 0 c\<^sub>2" by(fastforce intro:Labels_Base)
  hence "labels (if (b) c\<^sub>1 else c\<^sub>2) (#:c\<^sub>1 + 1) c\<^sub>2" by(fastforce dest:Labels_CondFalse)
  from `pred (\<lambda>s. interpret b s = Some false)\<^sub>\<surd> s`
  have "interpret b s = Some false" by simp
  hence "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>2,s,#:c\<^sub>1 + 1\<rangle>"
    by(rule StepCondFalse)
  with `labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)`
    `labels (if (b) c\<^sub>1 else c\<^sub>2) (#:c\<^sub>1 + 1) c\<^sub>2` show ?case by simp blast
next
  case (WCFG_CondThen c\<^sub>1 n et n' b c\<^sub>2)
  note IH = `\<And>l l'. \<lbrakk>n = (_ l _); n' = (_ l' _); transfer et s = s'; pred et s\<rbrakk>
    \<Longrightarrow> \<exists>c c'. c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels c\<^sub>1 l c \<and> labels c\<^sub>1 l' c'`
  from `n \<oplus> 1 = (_ l _)` obtain lx where "n = (_ lx _)" and [simp]:"l = lx + 1"
    by(cases n) auto
  from `n' \<oplus> 1 = (_ l' _)` obtain lx' where "n' = (_ lx' _)" and [simp]:"l' = lx' + 1"
    by(cases n') auto
  from IH[OF `n = (_ lx _)` `n' = (_ lx' _)` `transfer et s = s'` `pred et s`]
  obtain c c'  where "c\<^sub>1 \<turnstile> \<langle>c,s,lx\<rangle> \<leadsto> \<langle>c',s',lx'\<rangle>"
    and "labels c\<^sub>1 lx c" and "labels c\<^sub>1 lx' c'" by blast
  from `c\<^sub>1 \<turnstile> \<langle>c,s,lx\<rangle> \<leadsto> \<langle>c',s',lx'\<rangle>` have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
    by(fastforce intro:StepRecCond1)
  moreover 
  from `labels c\<^sub>1 lx c` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c"
    by(fastforce intro:Labels_CondTrue)
  moreover 
  from `labels c\<^sub>1 lx' c'` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l' c'"
    by(fastforce intro:Labels_CondTrue)
  ultimately show ?case by blast
next
  case (WCFG_CondElse c\<^sub>2 n et n' b c\<^sub>1)
  note IH = `\<And>l l'. \<lbrakk>n = (_ l _); n' = (_ l' _); transfer et s = s'; pred et s\<rbrakk>
    \<Longrightarrow> \<exists>c c'. c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels c\<^sub>2 l c \<and> labels c\<^sub>2 l' c'`
  from `n \<oplus> #:c\<^sub>1 + 1 = (_ l _)` obtain lx where "n = (_ lx _)" 
    and [simp]:"l = lx + #:c\<^sub>1 + 1"
    by(cases n) auto
  from `n' \<oplus> #:c\<^sub>1 + 1 = (_ l' _)` obtain lx' where "n' = (_ lx' _)" 
    and [simp]:"l' = lx' + #:c\<^sub>1 + 1"
    by(cases n') auto
  from IH[OF `n = (_ lx _)` `n' = (_ lx' _)` `transfer et s = s'` `pred et s`]
  obtain c c' where "c\<^sub>2 \<turnstile> \<langle>c,s,lx\<rangle> \<leadsto> \<langle>c',s',lx'\<rangle>"
    and "labels c\<^sub>2 lx c" and "labels c\<^sub>2 lx' c'" by blast
  from `c\<^sub>2 \<turnstile> \<langle>c,s,lx\<rangle> \<leadsto> \<langle>c',s',lx'\<rangle>` have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
    by(fastforce intro:StepRecCond2)
  moreover 
  from `labels c\<^sub>2 lx c` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c"
    by(fastforce intro:Labels_CondFalse)
  moreover 
  from `labels c\<^sub>2 lx' c'` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l' c'"
    by(fastforce intro:Labels_CondFalse)
  ultimately show ?case by blast
next
  case (WCFG_WhileTrue b cx)
  from `(_0_) \<oplus> 2 = (_ l' _)` have [simp]:"l' = 2" by simp
  from `transfer (\<lambda>s. interpret b s = Some true)\<^sub>\<surd> s = s'` have [simp]:"s' = s" by simp
  have "labels (while (b) cx) 0 (while (b) cx)"
    by(fastforce intro:Labels_Base)
  have "labels cx 0 cx" by(fastforce intro:Labels_Base)
  hence "labels (while (b) cx) 2 (cx;;while (b) cx)"
    by(fastforce dest:Labels_WhileBody)
  from `pred (\<lambda>s. interpret b s = Some true)\<^sub>\<surd> s` have "interpret b s = Some true" by simp
  hence "while (b) cx \<turnstile> \<langle>while (b) cx,s,0\<rangle> \<leadsto> \<langle>cx;;while (b) cx,s,2\<rangle>"
    by(rule StepWhileTrue)
  with `labels (while (b) cx) 0 (while (b) cx)`
    `labels (while (b) cx) 2 (cx;;while (b) cx)` show ?case by simp blast
next
  case (WCFG_WhileFalse b cx)
  from `transfer (\<lambda>s. interpret b s = Some false)\<^sub>\<surd> s = s'` have [simp]:"s' = s"
    by simp
  have "labels (while (b) cx) 0 (while (b) cx)" by(fastforce intro:Labels_Base)
  have "labels (while (b) cx) 1 Skip" by(fastforce intro:Labels_WhileExit)
  from `pred (\<lambda>s. interpret b s = Some false)\<^sub>\<surd> s` have "interpret b s = Some false"
    by simp
  hence "while (b) cx \<turnstile> \<langle>while (b) cx,s,0\<rangle> \<leadsto> \<langle>Skip,s,1\<rangle>"
    by(rule StepWhileFalse)
  with `labels (while (b) cx) 0 (while (b) cx)` `labels (while (b) cx) 1 Skip`
  show ?case by simp blast
next
  case (WCFG_WhileBody cx n et n' b)
  note IH = `\<And>l l'. \<lbrakk>n = (_ l _); n' = (_ l' _); transfer et s = s'; pred et s\<rbrakk>
    \<Longrightarrow> \<exists>c c'. cx \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels cx l c \<and> labels cx l' c'`
  from `n \<oplus> 2 = (_ l _)` obtain lx where "n = (_ lx _)" and [simp]:"l = lx + 2"
    by(cases n) auto
  from `n' \<oplus> 2 = (_ l' _)` obtain lx' where "n' = (_ lx' _)" 
    and [simp]:"l' = lx' + 2" by(cases n') auto
  from IH[OF `n = (_ lx _)` `n' = (_ lx' _)` `transfer et s = s'` `pred et s`]
  obtain c c' where "cx \<turnstile> \<langle>c,s,lx\<rangle> \<leadsto> \<langle>c',s',lx'\<rangle>"
    and "labels cx lx c" and "labels cx lx' c'" by blast
  hence "while (b) cx \<turnstile> \<langle>c;;while (b) cx,s,l\<rangle> \<leadsto> \<langle>c';;while (b) cx,s',l'\<rangle>"
    by(fastforce intro:StepRecWhile)
  moreover 
  from `labels cx lx c` have "labels (while (b) cx) l (c;;while (b) cx)"
    by(fastforce intro:Labels_WhileBody)
  moreover 
  from `labels cx lx' c'` have "labels (while (b) cx) l' (c';;while (b) cx)"
    by(fastforce intro:Labels_WhileBody)
  ultimately show ?case by blast
next
  case (WCFG_WhileBodyExit cx n et b)
  from `n \<oplus> 2 = (_ l _)` obtain lx where [simp]:"n = (_ lx _)" and [simp]:"l = lx + 2"
    by(cases n) auto
  from `cx \<turnstile> n -et\<rightarrow> (_Exit_)` have "labels cx lx Skip" and [simp]:"et = \<Up>id"
    by(auto dest:WCFG_edge_Exit_Skip)
  from `transfer et s = s'` have [simp]:"s' = s" by simp
  from `labels cx lx Skip` have "labels (while (b) cx) l (Skip;;while (b) cx)"
    by(fastforce intro:Labels_WhileBody)
  hence "while (b) cx \<turnstile> \<langle>Skip;;while (b) cx,s,l\<rangle> \<leadsto> \<langle>while (b) cx,s,0\<rangle>"
    by(rule StepSeqWhile)
  moreover
  have "labels (while (b) cx) 0 (while (b) cx)"
    by(fastforce intro:Labels_Base)
  ultimately show ?case 
    using `labels (while (b) cx) l (Skip;;while (b) cx)` by simp blast
qed


end
