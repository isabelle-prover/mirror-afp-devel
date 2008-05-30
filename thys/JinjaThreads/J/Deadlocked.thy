(*  Title:      JinjaThreads/J/Deadlocked.thy
    Author:     Andreas Lochbihler
*)

theory Deadlocked imports ProgressThreaded begin

lemma red_Lock_hext: 
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); hext (hp s) h \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"
apply(induct rule: red.induct)
apply(fastsimp intro: red.intros dest: hext_objarrD)+
done

lemma red_Join_hext:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; hext (hp s) h \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"
apply(induct rule: red.induct)
apply(fastsimp intro: red.intros dest: hext_objD hext_arrD)+
done

lemma red_Lock_wth:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); P,E,h \<turnstile> e : T \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"
proof(induct arbitrary: E T rule: red.induct)
  case (CallParams e s ta e' s' v M vs es E T)
  from `P,E,h \<turnstile> Val v\<bullet>M(map Val vs @ e # es) : T`
  have "\<exists>T'. P,E,h \<turnstile> e : T'"
    by(auto elim: WTrt_elim_cases simp add: list_all2_append1 list_all2_Cons1)
  with CallParams show ?case
    by(blast intro: red.CallParams)
next
  case (RedWait s a arrobj E T)
  from `P,E,h \<turnstile> addr a\<bullet>wait([]) : T`
  have "\<exists>arrobj. h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim: WTrt_elim_cases)
  thus ?case by(fastsimp intro: red.RedWait)
next
  case (RedNotify s a arrobj E T)
  from `P,E,h \<turnstile> addr a\<bullet>notify([]) : T`
  have "\<exists>arrobj. h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim: WTrt_elim_cases)
  thus ?case by(fastsimp intro: red.RedNotify)
next
  case (RedNotifyAll s a arrobj E T)
  from `P,E,h \<turnstile> addr a\<bullet>notifyAll([]) : T`
  have "\<exists>arrobj. h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim: WTrt_elim_cases)
  thus ?case by(fastsimp intro: red.RedNotifyAll)
next
  case (LockSynchronized s a arrobj e E T)
  from `P,E,h \<turnstile> sync(addr a) e : T`
  have "\<exists>arrobj. h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim: WTrt_elim_cases)
  thus ?case by(fastsimp intro: red.LockSynchronized)
qed(fastsimp intro: red.intros split: split_if_asm)+

lemma red_Join_wth:
  "\<lbrakk>P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; P,E,h \<turnstile> e : T; hext h (hp s) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"
proof(induct arbitrary: E T rule: red.induct)
  case (CallParams e s ta e' s' v M vs es E T)
  from `P,E,h \<turnstile> Val v\<bullet>M(map Val vs @ e # es) : T`
  have "\<exists>T'. P,E,h \<turnstile> e : T'"
    by(auto elim: WTrt_elim_cases simp add: list_all2_append1 list_all2_Cons1)
  with CallParams show ?case
    by(blast intro: red.CallParams)
next
  case (RedJoin s a C fs E T)
  from `P,E,h \<turnstile> addr a\<bullet>join([]) : T`
  have "\<exists>C' fs'. h a = \<lfloor>Obj C' fs'\<rfloor>"
    by(auto elim: WTrt_elim_cases split: heapobj.split_asm)
  then obtain C' fs' where "h a = \<lfloor>Obj C' fs'\<rfloor>" by blast
  moreover with `hext h (hp s)` `hp s a = \<lfloor>Obj C fs\<rfloor>`
  have "C' = C" by(auto dest: hext_objD)
  moreover note `P \<turnstile> C \<preceq>\<^sup>* Thread`
  ultimately show ?case
    by -(rule red.RedJoin, auto)
qed(fastsimp intro: red.intros split: split_if_asm)+

lemma red_wt_hconf_hext:
  assumes red: "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  and wt: "P,E,H \<turnstile> e : T"
  and hconf: "P \<turnstile> H \<surd>"
  and wf: "wf_J_prog P"
  and hext: "hext H (hp s)"
  shows "\<exists>ta' e' s'. P \<turnstile> \<langle>e, (H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> locks_a ta' = locks_a ta \<and> wset_a ta' = wset_a ta \<and> cond_a ta' = cond_a ta"
using red wt hext
proof(induct arbitrary: E T rule: red.induct)
  case (RedNew h a C FDTs h' l E T)
  show ?case
  proof(cases "new_Addr H")
    case None thus ?thesis
      by(fastsimp intro: RedNewFail)
  next
    case (Some a)
    with `P \<turnstile> C has_fields FDTs` show ?thesis
      by(fastsimp intro: red.RedNew)
  qed
next
  case (RedNewFail s C E T)
  show ?case
  proof(cases "new_Addr H")
    case None thus ?thesis
      by(fastsimp intro: red.RedNewFail)
  next
    case (Some a)
    with `P,E,H \<turnstile> new C : T` wf show ?thesis
      by(fastsimp del:exE intro!:RedNew simp add:new_Addr_def elim!:wf_Fields_Ex[THEN exE])
  qed
next
  case (RedNewArray h a i h' T l E T')
  show ?case
  proof(cases "new_Addr H")
    case None thus ?thesis using `0 \<le> i`
      by(fastsimp intro: red.RedNewArrayFail)
  next
    case (Some a)
    with `0 \<le> i` show ?thesis
      by(fastsimp intro: red.RedNewArray)
  qed
next
  case (RedNewArrayFail h i T l E T')
  show ?case
  proof(cases "new_Addr H")
    case None thus ?thesis using `0 \<le> i`
      by(fastsimp intro: red.RedNewArrayFail)
  next
    case (Some a)
    with `0 \<le> i` show ?thesis
      by(fastsimp intro: red.RedNewArray)
  qed
next
  case (RedCast s v U T E T')
  from `P,E,H \<turnstile> Cast T (Val v) : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T''
    assume wt: "P,E,H \<turnstile> Val v : T''" "T = T'"
    show ?thesis
    proof(cases "P \<turnstile> T'' \<le> T")
      case True
      with wt show ?thesis
	by(fastsimp intro: red.RedCast)
    next
      case False
      with wt show ?thesis
	by(fastsimp intro: red.RedCastFail)
    qed
  qed
next
  case (RedCastFail s v U T E T')
  from `P,E,H \<turnstile> Cast T (Val v) : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T''
    assume wt: "P,E,H \<turnstile> Val v : T''" "T = T'"
    show ?thesis
    proof(cases "P \<turnstile> T'' \<le> T")
      case True
      with wt show ?thesis
	by(fastsimp intro: red.RedCast)
    next
      case False
      with wt show ?thesis
	by(fastsimp intro: red.RedCastFail)
    qed
  qed
next
  case (RedAAccBounds s a T si el i E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> : T'` show ?case
  proof(rule WTrt_elim_cases)
    assume wt: "P,E,H \<turnstile> addr a : T'\<lfloor>\<rceil>"
    then obtain si' el' where Ha: "H a = \<lfloor>Arr T' si' el'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hext H (hp s)` `hp s a = \<lfloor>Arr T si el\<rfloor>` have si': "si = si'"
      by(auto dest!: hext_arrD)
    with Ha `i < 0 \<or> si \<le> i` show ?thesis
      by(fastsimp intro: red.RedAAccBounds)
  next
    assume wt: "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  qed
next
  case (RedAAcc s a T si el i E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> : T'` show ?case
  proof(rule WTrt_elim_cases)
    assume wt: "P,E,H \<turnstile> addr a : T'\<lfloor>\<rceil>"
    then obtain si' el' where Ha: "H a = \<lfloor>Arr T' si' el'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hext H (hp s)` `hp s a = \<lfloor>Arr T si el\<rfloor>` have si': "si = si'"
      by(auto dest!: hext_arrD)
    with Ha `0 \<le> i` `i < si` show ?thesis
      by(fastsimp intro: red.RedAAcc)
  next
    assume wt: "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  qed
next
  case (RedAAssBounds s a T si el i e E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val e : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T'' T'''
    assume wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
    then obtain si' el' where Ha: "H a = \<lfloor>Arr T'' si' el'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hext H (hp s)` `hp s a = \<lfloor>Arr T si el\<rfloor>` have si': "si = si'" and T'': "T'' = T"
      by(auto dest!: hext_arrD)
    with Ha `i < 0 \<or> si \<le> i` show ?thesis
      by(fastsimp intro: red.RedAAssBounds)
  next
    fix T''
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  qed
next
  case (RedAAssStore s a T si el i w U E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T'' T'''
    assume wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
      and wtw: "P,E,H \<turnstile> Val w : T'''"
    then obtain si' el' where Ha: "H a = \<lfloor>Arr T'' si' el'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hext H (hp s)` `hp s a = \<lfloor>Arr T si el\<rfloor>` have si': "si = si'" and T'': "T'' = T"
      by(auto dest!: hext_arrD)
    from `typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>` wtw `hext H (hp s)` have "typeof\<^bsub>H\<^esub> w = \<lfloor>U\<rfloor>" 
      by(auto dest: type_of_hext_type_of)
    with Ha `0 \<le> i` `i < si` `\<not> P \<turnstile> U \<le> T` T'' si' show ?thesis
      by(fastsimp intro: red.RedAAssStore)
  next
    fix T''
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  qed
next
  case (RedAAss h a T s el i w U h' l E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T'' T'''
    assume wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
      and wtw: "P,E,H \<turnstile> Val w : T'''"
    then obtain si' el' where Ha: "H a = \<lfloor>Arr T'' si' el'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hext H (hp (h, l))` `h a = \<lfloor>Arr T s el\<rfloor>` have si': "s = si'" and T'': "T'' = T"
      by(auto dest!: hext_arrD)
    from `typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>` wtw `hext H (hp (h, l))` have "typeof\<^bsub>H\<^esub> w = \<lfloor>U\<rfloor>" 
      by(auto dest: type_of_hext_type_of)
    with Ha `0 \<le> i` `i < s` `P \<turnstile> U \<le> T` T'' si' show ?thesis
      by(fastsimp intro: red.RedAAss)
  next
    fix T''
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  qed
next
  case (RedFAcc s a C fs F D v E T)
  from `P,E,H \<turnstile> addr a\<bullet>F{D} : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C'
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and has: "P \<turnstile> C' has F:T in D"
    then obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with hconf have "P,H \<turnstile> Obj C' fs' \<surd>" by(auto simp: hconf_def)
    with has have "\<exists>v. fs' (F, D) = \<lfloor>v\<rfloor>"
      by(fastsimp simp: oconf_def)
    with has fs' show ?thesis
      by(fastsimp intro: red.RedFAcc)
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  qed
next
  case (RedFAss h a C fs F D v l E T)
  from `P,E,H \<turnstile> addr a\<bullet>F{D} := Val v : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C' T' T2
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and has: "P \<turnstile> C' has F:T' in D"
      and wtv: "P,E,H \<turnstile> Val v : T2"
      and T2T: "P \<turnstile> T2 \<le> T'"
    moreover from wt obtain fs' where "H a = \<lfloor>Obj C' fs'\<rfloor>" 
      by(clarsimp, case_tac aa, auto)
    ultimately show ?thesis
      by(fastsimp intro: red.RedFAss)
  next
    fix T2
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  qed
next
  case (CallParams e s ta e' s' v M vs es E T)
  thus ?case
    by(fastsimp intro: red.CallParams simp add: list_all2_Cons1 list_all2_append1)
next
  case (RedCall s a C fs M Ts T pns body D vs E T')
  from `P,E,H \<turnstile> addr a\<bullet>M(map Val vs) : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix C' Ts' pns' body' D' Ts''
    assume wta: "P,E,H \<turnstile> addr a : Class C'"
      and sees: "P \<turnstile> C' sees M: Ts'\<rightarrow>T' = (pns', body') in D'"
      and wtes: "list_all2 (WellTypeRT.WTrt_syntax P E H) (map Val vs) Ts''"
      and widens: "P \<turnstile> Ts'' [\<le>] Ts'"
    from wta obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    moreover from wtes have "length vs = length Ts''"
      by(auto intro: map_eq_imp_length_eq')
    moreover from widens have "length Ts'' = length Ts'"
      by(auto dest: widens_lengthD)
    moreover from sees wf have "wf_mdecl wf_J_mdecl P D' (M, Ts', T', pns', body')"
      by(auto intro: sees_wf_mdecl)
    hence "length pns' = length Ts'"
      by(simp add: wf_mdecl_def)
    moreover from `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` fs' have "C = C'"
      by(auto dest: hext_objD)
    ultimately show ?thesis using sees
      by(fastsimp intro: red.RedCall)
  next
    fix Ts
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next
    fix C'
    assume sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
      and start: "M = start"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with sub start have False using `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
      by(auto dest: Thread_not_sees_method_start[OF wf])
    thus ?thesis ..
  next
    fix T'
    assume "M = wait"
    moreover
    from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` 
    obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(M, Ts, T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    ultimately have False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  next
    fix T'
    assume "M = notify"
    moreover
    from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` 
    obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(M, Ts, T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    ultimately have False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  next
    fix T'
    assume "M = notifyAll"
    moreover
    from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` 
    obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(M, Ts, T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    ultimately have False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  next
    fix C'
    assume sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
      and start: "M = join"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with sub start have False using `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
      by(auto dest: Thread_not_sees_method_join[OF wf])
    thus ?thesis ..
  qed
next
  case (RedNewThread s a C fs E T)
  from `P,E,H \<turnstile> addr a\<bullet>start([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C' pns' body' D'
    assume sees: "P \<turnstile> C' sees start: []\<rightarrow>T = (pns', body') in D'"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with `P \<turnstile> C \<preceq>\<^sup>* Thread` fs' sees wf have False
      by(auto simp: Method_def intro: Thread_no_sees_method_start[OF wf])
    thus ?thesis ..
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next
    fix C'
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with sub show ?thesis
      by(fastsimp intro: red.RedNewThread)
  qed
next
  case (RedNewThreadFail s a C fs E T)
  from `P,E,H \<turnstile> addr a\<bullet>start([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C' pns' body' D'
    assume sees: "P \<turnstile> C' sees start: []\<rightarrow>T = (pns', body') in D'"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with `P \<turnstile> C \<preceq>\<^sup>* Thread` fs' sees wf have False
      by(auto simp: Method_def intro: Thread_no_sees_method_start[OF wf])
    thus ?thesis ..
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next
    fix C'
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with sub show ?thesis
      by(fastsimp intro: red.RedNewThreadFail)
  qed
next
  case (RedWait s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>wait([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees wait: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(wait, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red.RedWait)+
next
  case (RedWaitFail s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>wait([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees wait: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(wait, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red.RedWaitFail)+
next
  case (RedNotify s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>notify([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees notify: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(notify, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red.RedNotify)+
next
  case (RedNotifyFail s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>notify([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees notify: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(notify, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red.RedNotifyFail)+
next
  case (RedNotifyAll s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>notifyAll([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees notifyAll: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(notifyAll, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red.RedNotifyAll)+
next
  case (RedNotifyAllFail s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>notifyAll([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees notifyAll: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(notifyAll, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red.RedNotifyAllFail)+
next
  case (RedJoin s a C fs E T)
  from `P,E,H \<turnstile> addr a\<bullet>join([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C' pns' body' D'
    assume sees: "P \<turnstile> C' sees join: []\<rightarrow>T = (pns', body') in D'"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with `P \<turnstile> C \<preceq>\<^sup>* Thread` fs' sees wf have False
      by(auto dest: Thread_not_sees_method_join[OF wf])
    thus ?thesis ..
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next
    fix C'
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(clarsimp, case_tac aa, auto)
    with sub show ?thesis
      by(fastsimp intro: red.RedJoin)
  qed
next
  case (BlockRedNone e h l V ta e' h' l' T E T')
  from `P,E,H \<turnstile> {V:T; e} : T'`
    `\<And>E T. \<lbrakk> P,E,H \<turnstile> e : T; hext H (hp (h, l(V := None))) \<rbrakk> \<Longrightarrow> \<exists>ta' e' s'. P \<turnstile> \<langle>e,(H, lcl (h, l(V := None)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>`
    `hext H (hp (h, l))`
  obtain ta' e' H' l'
    where "P \<turnstile> \<langle>e,(H, l(V := None))\<rangle> -ta'\<rightarrow> \<langle>e', (H', l')\<rangle>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by fastsimp
  with `\<not> assigned V e` show ?case
    by (cases "l' V") (fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next
  case (BlockRedSome e h l V ta e' h' l' v T E T')
  from `P,E,H \<turnstile> {V:T; e} : T'`
    `\<And>E T. \<lbrakk> P,E,H \<turnstile> e : T; hext H (hp (h, l(V := None))) \<rbrakk> \<Longrightarrow> \<exists>ta' e' s'. P \<turnstile> \<langle>e,(H, lcl (h, l(V := None)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>`
    `hext H (hp (h, l))`
  obtain ta' e' H' l'
    where "P \<turnstile> \<langle>e,(H, l(V := None))\<rangle> -ta'\<rightarrow> \<langle>e', (H', l')\<rangle>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by fastsimp
  with `\<not> assigned V e` show ?case
    by (cases "l' V") (fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next
  case (InitBlockRed e h l V v ta e' h' l' v' T E T')
  from `P,E,H \<turnstile> {V:T; V:=Val v;; e} : T'`
    `\<And>E T. \<lbrakk> P,E,H \<turnstile> e : T; hext H (hp (h, l(V \<mapsto> v))) \<rbrakk> \<Longrightarrow> \<exists>ta' e' s'. P \<turnstile> \<langle>e,(H, lcl (h, l(V \<mapsto> v)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>`
    `hext H (hp (h, l))`
  obtain ta' e' H' l'
    where "P \<turnstile> \<langle>e,(H, l(V \<mapsto> v))\<rangle> -ta'\<rightarrow> \<langle>e', (H', l')\<rangle>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by fastsimp
  moreover hence "\<exists>v. l' V = \<lfloor>v\<rfloor>"
    by(auto dest: red_lcl_incr)
  ultimately show ?case
    by(fastsimp intro: red.InitBlockRed)
next
  case (LockSynchronized s a arrobj e E T)
  from `P,E,H \<turnstile> sync(addr a) e : T` show ?case
  proof(rule WTrt_elim_cases)
    fix T
    assume "P,E,H \<turnstile> addr a : T" "is_refT T" "T \<noteq> NT"
    then obtain arrobj where "H a = \<lfloor>arrobj\<rfloor>"
      by(auto)
    thus ?thesis by(fastsimp intro: red.LockSynchronized)
  next
    fix T
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case (RedTryCatch s a D fs C V e2 E T)
  from `P,E,H \<turnstile> try Throw a catch(C V) e2 : T`
  show ?case
  proof(rule WTrt_elim_cases)
    fix T1
    assume "P,E,H \<turnstile> Throw a : T1"
    thus ?thesis
    proof(rule WTrt_elim_cases)
      fix T'
      assume "P,E,H \<turnstile> addr a : T'"
      with `hp s a = \<lfloor>Obj D fs\<rfloor>` `hext H (hp s)`
      obtain fs' where Ha: "H a = \<lfloor>Obj D fs'\<rfloor>" 
	by(clarsimp, case_tac aa, auto dest: hext_objD hext_arrD)
      with `P \<turnstile> D \<preceq>\<^sup>* C` show ?thesis
	by(fastsimp intro: red.RedTryCatch)
    qed
  qed
next
  case (RedTryFail s a D fs C V e2 E T)
  from `P,E,H \<turnstile> try Throw a catch(C V) e2 : T`
  show ?case
  proof(rule WTrt_elim_cases)
    fix T1
    assume "P,E,H \<turnstile> Throw a : T1"
    thus ?thesis
    proof(rule WTrt_elim_cases)
      fix T'
      assume "P,E,H \<turnstile> addr a : T'"
      with `hp s a = \<lfloor>Obj D fs\<rfloor>` `hext H (hp s)`
      obtain fs' where Ha: "H a = \<lfloor>Obj D fs'\<rfloor>" 
	by(clarsimp, case_tac aa, auto dest: hext_objD hext_arrD)
      with `\<not> P \<turnstile> D \<preceq>\<^sup>* C` show ?thesis
	apply -
	apply(rule exI)+
	apply(rule conjI)
	apply(rule red.RedTryFail)
	by(fastsimp)+
    qed
  qed
qed(fastsimp intro: red.intros)+
  
lemma must_sync_preserved:
  assumes ml: "P \<turnstile> \<langle>e, (h, x)\<rangle> \<wrong>"
  and wf: "wf_J_prog P"
  and wt: "P,E,h \<turnstile> e : T"
  and hext: "hext h h'"
  and hconf: "P \<turnstile> h \<surd>"
  shows "P \<turnstile> \<langle>e, (h', x)\<rangle> \<wrong>"
proof(rule multithreaded.must_syncI)
  fix ta X' h''
  assume "mred P ((e, snd (h', x)), fst (h', x)) ta (X', h'')"
  then obtain e' x'
    where e'x': "X' = (e', x')"
    and red: "P \<turnstile> \<langle>e, (h', x)\<rangle> -ta\<rightarrow> \<langle>e', (h'', x')\<rangle>"
    by(auto)
  from hext red wt wf hconf 
  have "\<exists>ta' e' s'. P \<turnstile> \<langle>e, (h, x)\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    by - (drule red_wt_hconf_hext, auto)
  then obtain ta' e' s'
    where red: "P \<turnstile> \<langle>e, (h, x)\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>"
    and ta'l: "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and ta'w: "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
    and ta'c: "\<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by blast
  from ml red have "(\<exists>l. Lock \<in> set (\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>)"
    by(cases s') (auto dest!: multithreaded.must_syncD)
  with ta'l ta'c show "(\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)" by simp
next
  from ml obtain ta ex m' where red: "mred P ((e, snd (h, x)), fst (h, x)) ta (ex, m')"
    by(auto elim: multithreaded.must_syncE)
  obtain e' x' where e'x': "ex = (e', x')" by (cases ex) auto
  with red have red': "P \<turnstile> \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (m', x')\<rangle>" by simp
  from red ml have "(\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
    by -(rule multithreaded.must_syncD)
  thus "\<exists>ta x' m'. mred P ((e, snd (h', x)), fst (h', x)) ta (x', m')"
  proof(rule disjE)
    assume "\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
    with red' hext have "P \<turnstile> \<langle>e, (h', x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>"
      by(auto dest: red_Lock_hext)
    thus ?thesis by(fastsimp)
  next
    assume "\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    with red' hext have "P \<turnstile> \<langle>e, (h', x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>"
      by(auto dest: red_Join_hext)
    thus ?thesis by(fastsimp)
  qed
qed

lemma can_lock_devreserp:
  "\<lbrakk> P \<turnstile> \<langle>e, (h', l)\<rangle> L \<wrong>; P,E,h \<turnstile> e : T; L \<noteq> {}; hext h h' \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, (h, l)\<rangle> L \<wrong>"
apply(erule multithreaded.can_syncE)
apply(case_tac x', auto elim!: collect_locksE)
 apply(drule red_Lock_wth)
 apply(auto intro: multithreaded.can_syncI)
apply(drule red_Join_wth)
apply(auto intro: multithreaded.can_syncI)
done


lemma preserve_deadlocked:
  assumes wf: "wf_J_prog P"
  and st: "sconf_type_ts_ok P Es (thr S) (shr S)"
  and da: "def_ass_ts_ok (thr S) (shr S)"
  shows "preserve_deadlocked final_expr (mred P) S"
proof -
  { fix tta s t' ta' s' t x ln
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s"
      and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
      and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    obtain e l where x [simp]: "x = (e, l)" by(cases x) auto
    let ?Es' = "upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) tta\<down>)"
    from st Red have st': "sconf_type_ts_ok P ?Es' (thr s) (shr s)"
      by(auto dest: RedT_invariant_sconf_type[OF wf])
    with tst obtain E T where Est: "?Es' t = \<lfloor>(E, T)\<rfloor>" 
      and stt: "sconf_type_ok P (E, T) e (shr s) l" by(auto dest!: ts_invD)
    from stt have hconf: "P \<turnstile> shr s \<surd>"
      by(simp add: sconf_type_ok_def sconf_def)
    from stt obtain T' where wte: "P,E,shr s \<turnstile> e : T'"
      by(auto simp add: sconf_type_ok_def type_ok_def)
    from red have hext: "hext (shr s) (shr s')"
      by(cases s, cases s')(auto dest: redT_hext_incr)

    { assume "multithreaded.must_sync (mred P) x (shr s)"
      hence ml: "P \<turnstile> \<langle>e, (shr s, l)\<rangle> \<wrong>" by auto
      from this and wf wte hext hconf
      have "P \<turnstile> \<langle>e, (shr s', l)\<rangle> \<wrong>" by (rule must_sync_preserved)
      hence "multithreaded.must_sync (mred P) x (shr s')" by simp }
    note ml = this
    { fix L
      assume "multithreaded.can_sync (mred P) x (shr s') L"
	and L: "L \<noteq> {}"
      hence cl: "P \<turnstile> \<langle>e, (shr s', l)\<rangle> L \<wrong>" by auto
      with wte L hext have "P \<turnstile> \<langle>e, (shr s, l)\<rangle> L \<wrong>"
	by -(rule can_lock_devreserp)
      hence "\<exists>L'\<subseteq>L. multithreaded.can_sync (mred P) x (shr s) L'"
	by(auto) }
    note this ml }
  thus ?thesis by(unfold_locales)
qed

end
