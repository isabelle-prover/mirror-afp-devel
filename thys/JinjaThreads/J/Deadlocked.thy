(*  Title:      JinjaThreads/J/Deadlocked.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Preservation of deadlock} *}

theory Deadlocked imports TypeSafeThreaded begin

lemma red_Lock_hext: 
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); hext (hp s) h \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"
proof(induct rule: red.induct)
  prefer 56
  case (SynchronizedWait e s ta e' s' a was)
  from `Lock \<in> set (\<lbrace>ta\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l)`
  have "Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
    by(cases ta, auto split: split_if_asm)
  with SynchronizedWait show ?case by (auto intro: red.SynchronizedWait)
qed(fastsimp intro: red.intros dest: hext_objarrD)+

lemma red_Lock_wth:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); P,E,h \<turnstile> e : T \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"
proof(induct arbitrary: E T rule: red.induct)
  prefer 36
  case (CallParams e s ta e' s' v M vs es E T)
  from `P,E,h \<turnstile> Val v\<bullet>M(map Val vs @ e # es) : T`
  have "\<exists>T'. P,E,h \<turnstile> e : T'"
    by(auto elim: WTrt_elim_cases simp add: list_all2_append1 list_all2_Cons1)
  with CallParams show ?case
    by(blast intro: red.CallParams)
next
  prefer 39
  case (RedWait s a arrobj E T)
  from `P,E,h \<turnstile> addr a\<bullet>wait([]) : T`
  have "\<exists>arrobj. h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim: WTrt_elim_cases)
  thus ?case by(fastsimp intro: red.RedWait)
next
  prefer 40
  case (RedNotify s a arrobj E T)
  from `P,E,h \<turnstile> addr a\<bullet>notify([]) : T`
  have "\<exists>arrobj. h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim: WTrt_elim_cases)
  thus ?case by(fastsimp intro: red.RedNotify)
next
  prefer 41
  case (RedNotifyAll s a arrobj E T)
  from `P,E,h \<turnstile> addr a\<bullet>notifyAll([]) : T`
  have "\<exists>arrobj. h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim: WTrt_elim_cases)
  thus ?case by(fastsimp intro: red.RedNotifyAll)
qed(fastsimp intro: red.intros split: split_if_asm)+



lemma red_wt_hconf_hext:
  assumes red: "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  and wt: "P,E,H \<turnstile> e : T"
  and hconf: "P \<turnstile> H \<surd>"
  and wf: "wf_J_prog P"
  and hext: "hext H (hp s)"
  shows "\<exists>ta' e' s'. P \<turnstile> \<langle>e, (H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> locks_a ta' = locks_a ta \<and> wset_a ta' = wset_a ta"
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
next prefer 2
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
next prefer 3
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
next prefer 4
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
next prefer 4
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
next prefer 13
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
next prefer 13
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
next prefer 17
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
next prefer 17
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
next prefer 17
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
next prefer 18
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
next prefer 21
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
next prefer 23
  case (CallParams e s ta e' s' v M vs es E T)
  thus ?case
    by(fastsimp intro: red.CallParams simp add: list_all2_Cons1 list_all2_append1)
next prefer 23
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
    moreover note `\<not> threadstart P C M`
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
      by(auto simp: Method_def intro: Thread_no_sees_method_start[OF wf])
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
  qed
next prefer 23
  case (RedNewThread s a C fs t E T)
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
  qed(simp_all add: start_def wait_def notify_def notifyAll_def)
next prefer 23
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
  qed(simp_all add: start_def wait_def notify_def notifyAll_def)
next prefer 23
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
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next prefer 2
    fix T
    assume "P,E,H \<turnstile> addr a : T"
    then obtain arrobj where "H a = \<lfloor>arrobj\<rfloor>"
      by(auto)
    thus ?thesis by(fastsimp intro: red.RedWait)
  qed(simp_all add: start_def wait_def notify_def notifyAll_def)
next prefer 23
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
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next prefer 2
    fix T
    assume "P,E,H \<turnstile> addr a : T"
    then obtain arrobj where "H a = \<lfloor>arrobj\<rfloor>"
      by(auto)
    thus ?thesis by(fastsimp intro: red.RedWaitFail)
  qed(simp_all add: start_def wait_def notify_def notifyAll_def)
next prefer 23
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
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next prefer 3
    fix T
    assume "P,E,H \<turnstile> addr a : T"
    then obtain arrobj where "H a = \<lfloor>arrobj\<rfloor>"
      by(auto)
    thus ?thesis by(fastsimp intro: red.RedNotify)
  qed(simp_all add: start_def wait_def notify_def notifyAll_def)
next prefer 23
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
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next prefer 3
    fix T
    assume "P,E,H \<turnstile> addr a : T"
    then obtain arrobj where "H a = \<lfloor>arrobj\<rfloor>"
      by(auto)
    thus ?thesis by(fastsimp intro: red.RedNotifyFail)
  qed(simp_all add: start_def wait_def notify_def notifyAll_def)
next prefer 23
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
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next prefer 4
    fix T
    assume "P,E,H \<turnstile> addr a : T"
    then obtain arrobj where "H a = \<lfloor>arrobj\<rfloor>"
      by(auto)
    thus ?thesis by(fastsimp intro: red.RedNotifyAll)
  qed(simp_all add: start_def wait_def notify_def notifyAll_def)
next prefer 23
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
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp, case_tac aa, auto)
    thus ?thesis ..
  next prefer 4
    fix T
    assume "P,E,H \<turnstile> addr a : T"
    then obtain arrobj where "H a = \<lfloor>arrobj\<rfloor>"
      by(auto)
    thus ?thesis by(fastsimp intro: red.RedNotifyAllFail)
  qed(simp_all add: start_def wait_def notify_def notifyAll_def)
next prefer 24
  case (BlockRedNone e h l V ta e' h' l' T E T')
  from `P,E,H \<turnstile> {V:T; e} : T'`
    `\<And>E T. \<lbrakk> P,E,H \<turnstile> e : T; hext H (hp (h, l(V := None))) \<rbrakk> \<Longrightarrow> \<exists>ta' e' s'. P \<turnstile> \<langle>e,(H, lcl (h, l(V := None)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>`
    `hext H (hp (h, l))`
  obtain ta' e' H' l'
    where "P \<turnstile> \<langle>e,(H, l(V := None))\<rangle> -ta'\<rightarrow> \<langle>e', (H', l')\<rangle>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by fastsimp
  with `\<not> assigned V e` show ?case
    apply(cases "l' V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next prefer 24
  case (BlockRedSome e h l V ta e' h' l' v T E T')
  from `P,E,H \<turnstile> {V:T; e} : T'`
    `\<And>E T. \<lbrakk> P,E,H \<turnstile> e : T; hext H (hp (h, l(V := None))) \<rbrakk> \<Longrightarrow> \<exists>ta' e' s'. P \<turnstile> \<langle>e,(H, lcl (h, l(V := None)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>`
    `hext H (hp (h, l))`
  obtain ta' e' H' l'
    where "P \<turnstile> \<langle>e,(H, l(V := None))\<rangle> -ta'\<rightarrow> \<langle>e', (H', l')\<rangle>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by fastsimp
  with `\<not> assigned V e` show ?case
    apply(cases "l' V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next prefer 24
  case (InitBlockRed e h l V v ta e' h' l' v' T E T')
  from `P,E,H \<turnstile> {V:T; V:=Val v;; e} : T'`
    `\<And>E T. \<lbrakk> P,E,H \<turnstile> e : T; hext H (hp (h, l(V \<mapsto> v))) \<rbrakk> \<Longrightarrow> \<exists>ta' e' s'. P \<turnstile> \<langle>e,(H, lcl (h, l(V \<mapsto> v)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>`
    `hext H (hp (h, l))`
  obtain ta' e' H' l'
    where "P \<turnstile> \<langle>e,(H, l(V \<mapsto> v))\<rangle> -ta'\<rightarrow> \<langle>e', (H', l')\<rangle>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by fastsimp
  moreover hence "\<exists>v. l' V = \<lfloor>v\<rfloor>"
    by(auto dest: red_lcl_incr)
  ultimately show ?case
    by(fastsimp intro: red.InitBlockRed)
next prefer 29
  case (SynchronizedRed2 e s ta e' s' a E T)
  from `P,E,H \<turnstile> sync(locked(a)) e : T`
    `\<And>E T. \<lbrakk> P,E,H \<turnstile> e : T; hext H (hp s) \<rbrakk> \<Longrightarrow> \<exists>ta' e' s'. P \<turnstile> \<langle>e,(H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>`
    `hext H (hp s)`
  obtain ta' e' s'
    where "P \<turnstile> \<langle>e,(H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by fastsimp
  with `\<forall>was. \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<noteq> Suspend a # was` show ?case
    by(fastsimp intro: red.SynchronizedRed2)
next prefer 29
  case (SynchronizedWait e s ta e' s' a was E T)
  from `P,E,H \<turnstile> sync(locked(a)) e : T`
    `\<And>E T. \<lbrakk> P,E,H \<turnstile> e : T; hext H (hp s) \<rbrakk> \<Longrightarrow> \<exists>ta' e' s'. P \<turnstile> \<langle>e,(H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>`
    `hext H (hp s)`
  obtain ta' e' s'
    where "P \<turnstile> \<langle>e,(H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by fastsimp
  with `\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = Suspend a # was` show ?case
    apply(cases ta, cases ta')
    apply(drule red.SynchronizedWait)
    by(fastsimp)+
next prefer 40
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
next prefer 40
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
  
lemma must_lock_preserved:
  assumes ml: "P \<turnstile> \<langle>e, (h, x)\<rangle> \<wrong>"
  and wf: "wf_J_prog P"
  and wt: "P,E,h \<turnstile> e : T"
  and hext: "hext h h'"
  and hconf: "P \<turnstile> h \<surd>"
  shows "P \<turnstile> \<langle>e, (h', x)\<rangle> \<wrong>"
proof(rule multithreaded.must_lockI)
  fix ta X' h''
  assume "(((e, snd (h', x)), fst (h', x)), ta, X', h'') \<in> mred P"
  then obtain e' x'
    where e'x': "X' = (e', x')"
    and red: "P \<turnstile> \<langle>e, (h', x)\<rangle> -ta\<rightarrow> \<langle>e', (h'', x')\<rangle>"
    by(auto)
  from hext red wt wf hconf 
  have "\<exists>ta' e' s'. P \<turnstile> \<langle>e, (h, x)\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
    by - (drule red_wt_hconf_hext, auto)
  then obtain ta' e' s'
    where red: "P \<turnstile> \<langle>e, (h, x)\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>"
    and ta'l: "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and ta'w: "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by blast
  from ml red have "\<exists>l. Lock \<in> set (\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> l)"
    by(cases s', auto dest!: multithreaded.must_lockD)
  with ta'l show "\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)" by simp
qed

lemma can_lock_preserved:
  assumes cl: "P \<turnstile> \<langle>e, (h, x)\<rangle> L \<wrong>"
  and Lnempty: "l \<in> L"
  and hext: "hext h h'"
  shows "\<exists>L. P \<turnstile> \<langle>e, (h', x)\<rangle> L \<wrong>"
using cl
proof(rule multithreaded.can_lockE)
  fix ta ex m'
  assume red: "(((e, snd (h, x)), fst (h, x)), ta, ex, m') \<in> mred P"
    and L: "L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  then obtain e' x' where e'x': "ex = (e', x')" by (cases ex, auto)
  with red have "P \<turnstile> \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (m', x')\<rangle>" by simp
  with Lnempty hext L have "P \<turnstile> \<langle>e, (h', x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>"
    apply(cases ta)
    apply(drule red_Lock_hext)
    by(auto elim: collect_locksE)
  with L Lnempty show ?thesis
    by(fastsimp intro: multithreaded.can_lockI)
qed

lemma can_lock_devreserp:
  "\<lbrakk> P \<turnstile> \<langle>e, (h', l)\<rangle> L \<wrong>; P,E,h \<turnstile> e : T; L \<noteq> {} \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, (h, l)\<rangle> L \<wrong>"
apply(erule multithreaded.can_lockE)
apply(case_tac x', auto elim!: collect_locksE)
apply(drule red_Lock_wth)
apply(auto intro: multithreaded.can_lockI)
done

lemma red_deadlocked_subset:
  assumes wf: "wf_J_prog P"
  and wt: "wt_ts_ok P ts m"
  and hconf: "P \<turnstile> m \<surd>"
  and red: "P \<turnstile> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>"
  shows "progress.deadlocked (mred P) final_expr (ls, (ts, m), ws) \<subseteq> progress.deadlocked (mred P) final_expr (ls', (ts', m'), ws')"
proof -
  from red have hext: "hext m m'"
    by(rule redT_hext_incr)
  from red
  show ?thesis
  proof(rule red_mthr_progress.redT_deadlocked_subset)
    fix t x
    assume "thr (ls, (ts, m), ws) t = \<lfloor>x\<rfloor>"
      and "multithreaded.must_lock (mred P) x (shr (ls, (ts, m), ws))"
    moreover
    obtain e l where el: "x = (e, l)" by (cases x, auto)
    ultimately have tst: "ts t = \<lfloor>x\<rfloor>" 
      and ml: "P \<turnstile> \<langle>e, (m, l)\<rangle> \<wrong>" by auto
    from tst wt el obtain E T where wte: "P,E,m \<turnstile> e : T"
      by(auto dest!: ts_okD)
    with ml wf hconf hext have "P \<turnstile> \<langle>e, (m', l)\<rangle> \<wrong>"
      by -(rule must_lock_preserved)
    with el show "multithreaded.must_lock (mred P) x (shr (ls', (ts', m'), ws'))"
      by(simp)
  next
    fix t x L
    assume "multithreaded.can_lock (mred P) x (shr (ls, (ts, m), ws)) L"
      and L: "L \<noteq> {}"
    moreover
    obtain e l where el: "x = (e, l)" by (cases x, auto)
    ultimately have cl: "P \<turnstile> \<langle>e, (m, l)\<rangle> L \<wrong>" by auto
    moreover from L obtain l' where "l' \<in> L" by auto
    ultimately have "\<exists>L. P \<turnstile> \<langle>e, (m', l)\<rangle> L \<wrong>" using hext
      by(rule can_lock_preserved)
    with el show "\<exists>L. multithreaded.can_lock (mred P) x (shr (ls', (ts', m'), ws')) L"
      by(simp)
  next
    fix t x L
    assume "thr (ls, (ts, m), ws) t = \<lfloor>x\<rfloor>"
      and "multithreaded.can_lock (mred P) x (shr (ls', (ts', m'), ws')) L"
      and L: "L \<noteq> {}"
    moreover
    obtain e l where el: "x = (e, l)" by (cases x, auto)
    ultimately have tst: "ts t = \<lfloor>x\<rfloor>" 
      and cl: "P \<turnstile> \<langle>e, (m', l)\<rangle> L \<wrong>" by auto
    from tst wt el obtain E T where wte: "P,E,m \<turnstile> e : T"
      by(auto dest!: ts_okD)
    with L cl have "P \<turnstile> \<langle>e, (m, l)\<rangle> L \<wrong>"
      by -(rule can_lock_devreserp)
    with el show "\<exists>L'\<subseteq>L. multithreaded.can_lock (mred P) x (shr (ls, (ts, m), ws)) L'"
      by auto
  qed
qed

declare [[unify_search_bound = 40, unify_trace_bound = 40]]

lemma Red_deadlocked_subset:
  assumes wf: "wf_J_prog P"
  and wt: "sconf_subject_ts_ok P I ts m"
  and da: "def_ass_ts_ok ts m"
  and red: "P \<turnstile> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>"
  shows "progress.deadlocked (mred P) final_expr (ls, (ts, m), ws) \<subseteq> progress.deadlocked (mred P) final_expr (ls', (ts', m'), ws')"
using red wt da
proof(induct rule: multithreaded.RedT_induct4[where r="mred P", consumes 1, case_names refl step])
  case refl thus ?case by simp
next
  case (step ls ts m ws ttas ls' ts' m' ws' t ta ls'' ts'' m'' ws'')
  note Red = `P \<turnstile> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>`
  note red = `P \<turnstile> \<langle>ls', (ts', m'), ws'\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls'', (ts'', m''), ws''\<rangle>`
  note sc = `sconf_subject_ts_ok P I ts m`
  note da = `def_ass_ts_ok ts m`
  with wf Red have da': "def_ass_ts_ok ts' m'"
    by(rule RedT_preserves_defass)
  moreover
  from da Red wf sc
  have sc': "sconf_subject_ts_ok P (upd_invs I (\<lambda>ET (e, x) m. sconf_subject_ok P ET e m x) (\<down>map (thr_a \<circ> snd) ttas\<down>)) ts' m'"
    by -(rule RedT_invariant_sconf_subject)
  hence "wt_ts_ok P ts' m'"
    by(rule sconf_subject_es_ok_wt_es_ok)
  moreover
  from red obtain x' where "ts' t = \<lfloor>x'\<rfloor>"
    by(fastsimp elim!: multithreaded.redT.cases)
  with sc' have "P \<turnstile> m' \<surd>"
    by(auto simp add: sconf_subject_ok_def sconf_def dest: ts_invD)
  ultimately have "progress.deadlocked (mred P) final_expr (ls', (ts', m'), ws') \<subseteq> progress.deadlocked (mred P) final_expr (ls'', (ts'', m''), ws'')" using red
    by -(rule red_deadlocked_subset[OF wf])
  moreover
  from sc da 
    `\<lbrakk>sconf_subject_ts_ok P I ts m; def_ass_ts_ok ts m\<rbrakk>
        \<Longrightarrow> progress.deadlocked (mred P) final_expr (ls, (ts, m), ws) \<subseteq> progress.deadlocked (mred P) final_expr (ls', (ts', m'), ws')`
  have "progress.deadlocked (mred P) final_expr (ls, (ts, m), ws) \<subseteq> progress.deadlocked (mred P) final_expr (ls', (ts', m'), ws')" by blast
  ultimately show ?case by blast
qed


end
