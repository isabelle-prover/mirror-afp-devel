(*  Title:      JinjaThreads/Framework/FWProgress.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Progress theorem for the multithreaded semantics} *}

theory FWProgress imports FWDeadlock FWWellformSem begin

locale progress = final_thread_wf final r + wf_progress final r start_state + wf_red final r start_state
  for final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80)
  and start_state :: "('l,'t,'x,'m,'w) state" +
  fixes deadlock :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool"
  assumes waiting_deadlock:
    "\<lbrakk> start_state -\<triangleright>ttas\<rightarrow>* s; not_final_thread s t;
       \<And>t x LT. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None; t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<rbrakk>
                \<Longrightarrow> \<exists>t'. \<exists>lt \<in> LT. must_wait s t lt t';
       \<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None; ln\<^sub>f l > 0 \<rbrakk> \<Longrightarrow> \<exists>l'. ln\<^sub>f l' > 0 \<and> \<not> may_lock ((locks s)\<^sub>f l') t \<rbrakk>
     \<Longrightarrow> deadlock s"
begin

lemma redTW_progress_not_Suspend:
  assumes Red: "start_state -\<triangleright>tta\<rightarrow>* (ls, (ts, m), ws)"
  and t: "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>" "ws t = None" "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
  and m'': "interrupted_mem_reds ts ws m' m''"
  and wa: "\<And>w. wa \<noteq> Suspend w"
  and ws'ws: "ws' \<subseteq>\<^sub>m ws"
  and ts'ts: "ts' |` dom ws' = ts |` dom ws'"
  shows "\<exists>ts'' m''' ws'' obs. redTW t wa (ls', (ts', m''), ws') obs (ls', (ts'', m'''), ws'') \<and> 
                          interrupted_mem_reds ts ws m'' m''' \<and> ws'' \<subseteq>\<^sub>m ws' \<and>
                          ts'' |` dom ws'' = ts |` dom ws''"
proof(cases wa)
  case Suspend with wa show ?thesis by fastsimp
next
  case (Notify w)
  show ?thesis
  proof(cases "\<exists>t. ws' t = \<lfloor>w\<rfloor>")
    case False
    hence "redTW t wa (ls', (ts', m''), ws') [] (ls', (ts', m''), ws')" unfolding Notify
      by(auto intro: redTW_NotifyNone)
    with ws'ws ts'ts show ?thesis by fastsimp
  next
    case True
    then obtain t' where "ws' t' = \<lfloor>w\<rfloor>" ..
    with ws'ws have "ws t' = \<lfloor>w\<rfloor>" by(auto dest: map_le_SomeD)
    show ?thesis
    proof(cases "ts' t'")
      case None
      with `ws' t' = \<lfloor>w\<rfloor>`
      have "redTW t wa (ls', (ts', m''), ws') [] (ls', (ts', m''), ws'(t' := None))"
        unfolding Notify by(auto intro: redTW_NotifySome simp add: expand_fun_eq)
      moreover from ts'ts have "ts' |` dom (ws'(t' := None)) = ts |` dom (ws'(t' := None))"
        by(auto simp add: expand_fun_eq restrict_map_def split: split_if_asm)
      ultimately show ?thesis by fastsimp
    next
      case (Some a)
      then obtain X LN where "ts' t' = \<lfloor>(X, LN)\<rfloor>" by(cases a) auto
      with `ws' t' = \<lfloor>w\<rfloor>` ts'ts have "ts t' = \<lfloor>(X, LN)\<rfloor>"
        by(auto simp add: restrict_map_def expand_fun_eq split: split_if_asm)
      from wf_red_wait[OF Red, simplified, OF `ts t' = \<lfloor>(X, LN)\<rfloor>` `ws t' = \<lfloor>w\<rfloor>` t m'']
      obtain X' where red: "t' \<turnstile> \<langle>X, m''\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified \<rbrace>\<rightarrow> \<langle>X', m''\<rangle>" by auto
      with `ws' t' = \<lfloor>w\<rfloor>` `ts' t' = \<lfloor>(X, LN)\<rfloor>`
      have "redTW t wa (ls', (ts', m''), ws') [] (ls', (ts'(t' \<mapsto> (X', LN)), m''), ws'(t' := None))"
        unfolding Notify by(auto intro: redTW_NotifySome)
      moreover have "ws'(t' := None) \<subseteq>\<^sub>m ws'" by auto
      moreover have "ts'(t' \<mapsto> (X', LN)) |` dom (ws'(t' := None)) = ts |` dom (ws'(t' := None))"
        using ts'ts by(auto simp add: restrict_map_def expand_fun_eq split_if_asm)
      ultimately show ?thesis by blast
    qed
  qed
next
  case (NotifyAll w)
  let ?x' = "\<lambda>t'. if (ws' t' = \<lfloor>w\<rfloor>) then SOME x'. t' \<turnstile> \<langle>fst (the (ts' t')), m''\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> \<langle>x', m''\<rangle> else undefined"
  let ?ts'' = "(\<lambda>t'. if (ws' t' = \<lfloor>w\<rfloor>) then Option.map (\<lambda>(x, ln). (?x' t', ln)) (ts' t') else ts' t')"
  let ?ws' = "\<lambda>t'. if ws' t' = \<lfloor>w\<rfloor> then None else ws' t'"
  { fix t' X LN
    assume "ws' t' = \<lfloor>w\<rfloor>"
      and "ts' t' = \<lfloor>(X, LN)\<rfloor>"
    hence "ts t' = \<lfloor>(X, LN)\<rfloor>" using ts'ts
      by(auto simp add: restrict_map_def expand_fun_eq split: split_if_asm)
    let ?P = "\<lambda>x'. t' \<turnstile> \<langle>X, m''\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> \<langle>x', m''\<rangle>"
    from `ws' t' = \<lfloor>w\<rfloor>` ws'ws have "ws t' = \<lfloor>w\<rfloor>" by(auto dest: map_le_SomeD)
    from wf_red_wait[OF Red, simplified, OF `ts t' = \<lfloor>(X, LN)\<rfloor>` `ws t' = \<lfloor>w\<rfloor>` t m'']
    have "Ex ?P" by simp
    hence "?P (Eps ?P)" by(rule someI_ex) }
  hence "redTW t wa (ls', (ts', m''), ws') [] (ls', (?ts'', m''), ?ws')"
    unfolding NotifyAll by -(rule redTW_NotifyAll[where x'="?x'"], simp_all cong: if_cong)
  moreover have "?ws' \<subseteq>\<^sub>m ws'" by(auto simp add: map_le_def)
  moreover have "?ts'' |` dom ?ws' = ts |` dom ?ws'" using ts'ts
    by(fastsimp simp add: restrict_map_def expand_fun_eq split: split_if_asm)
  ultimately show ?thesis by blast
next
  case (Interrupt t')
  show ?thesis
  proof(cases "ws' t'")
    case None
    hence "redTW t wa (ls', (ts', m''), ws') [] (ls', (ts', m''), ws')" 
      unfolding Interrupt by(auto intro: redTW_InterruptNone)
    with ws'ws ts'ts show ?thesis by fastsimp
  next
    case (Some w)
    with ws'ws have "ws t' = \<lfloor>w\<rfloor>" by(auto dest: map_le_SomeD)
    show ?thesis
    proof(cases "ts' t'")
      case None
      hence "redTW t wa (ls', (ts', m''), ws') (observable_of \<lbrace> (\<epsilon>\<lbrace>\<^bsub>c\<^esub> Interrupted \<rbrace>) :: ('l, 't, 'x, 'm, 'w, 'o list) thread_action\<rbrace>\<^bsub>o\<^esub>) (ls', (ts', m''), ws'(t' := None))"
        using Some unfolding Interrupt
        by -(rule redTW_InterruptWait, auto simp add: expand_fun_eq is_Interrupted_ta_def ta_upd_simps)
      moreover have "ts' |` dom (ws'(t' := None)) = ts |` dom (ws'(t' := None))"
        using ts'ts by(auto simp add: restrict_map_def expand_fun_eq split: split_if_asm)
      ultimately show ?thesis by fastsimp
    next
      case (Some a)
      then obtain X LN where "ts' t' = \<lfloor>(X, LN)\<rfloor>" by(cases a)(auto)
      with ts'ts `ws' t' = \<lfloor>w\<rfloor>` have "ts t' = \<lfloor>(X, LN)\<rfloor>"
        by(auto simp add: restrict_map_def expand_fun_eq split: split_if_asm)
      from wf_red_wait[OF Red, simplified, OF `ts t' = \<lfloor>(X, LN)\<rfloor>` `ws t' = \<lfloor>w\<rfloor>` t m'']
      obtain X' m''' ta where red: "t' \<turnstile> \<langle>X, m''\<rangle> -ta\<rightarrow> \<langle>X', m'''\<rangle>" 
        and ta: "is_Interrupted_ta ta" by auto
      with `ts' t' = \<lfloor>(X, LN)\<rfloor>` `ws' t' = \<lfloor>w\<rfloor>`
      have "redTW t wa (ls', (ts', m''), ws') (observable_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ls', (ts'(t' \<mapsto> (X', LN)), m'''), ws'(t' := None))"
        unfolding Interrupt by(auto intro: redTW_InterruptWait)
      moreover from `ts t' = \<lfloor>(X, LN)\<rfloor>` `ws t' = \<lfloor>w\<rfloor>` red ta
      have "interrupted_mem_reds ts ws m'' m'''"
        by(blast intro: interrupted_mem_red.intros)
      moreover have "ws'(t' := None) \<subseteq>\<^sub>m ws'" by simp
      moreover have "(ts'(t' \<mapsto> (X', LN))) |` dom (ws'(t' := None)) = ts |` dom (ws'(t' := None))"
        using ts'ts by(auto simp add: restrict_map_def expand_fun_eq split: split_if_asm)
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma redTWs_progress_not_Suspend:
  assumes Red: "start_state -\<triangleright>tta\<rightarrow>* (ls, (ts, m), ws)"
  and t: "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>" "ws t = None" "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
  and m'': "interrupted_mem_reds ts ws m' m''"
  and wa: "\<And>w. Suspend w \<notin> set was"
  and ws'ws: "ws' \<subseteq>\<^sub>m ws"
  and ts'ts: "ts' |` dom ws' = ts |` dom ws'"
  shows "\<exists>ts'' m''' ws'' obs. redTWs t was (ls', (ts', m''), ws') obs (ls', (ts'', m'''), ws'') \<and> 
                              interrupted_mem_reds ts ws m'' m''' \<and> ws'' \<subseteq>\<^sub>m ws' \<and>
                              ts'' |` dom ws'' = ts |` dom ws''"
using wa
proof(induct was rule: rev_induct)
  case Nil thus ?case using ts'ts by fastsimp
next
  case (snoc wa was)
  then obtain ts'' m''' ws'' obs
    where redTWs: "redTWs t was (ls', (ts', m''), ws') obs (ls', (ts'', m'''), ws'')"
    and m''': "interrupted_mem_reds ts ws m'' m'''"
    and ws''ws': "ws'' \<subseteq>\<^sub>m ws'"
    and ts''ts: "ts'' |` dom ws'' = ts |` dom ws''" by auto
  from m'' m''' have m': "interrupted_mem_reds ts ws m' m'''" by(blast intro: rtranclp_trans)
  from `\<And>w. Suspend w \<notin> set (was @ [wa])` have wa: "\<And>w. wa \<noteq> Suspend w" by auto
  from ws''ws' ws'ws have "ws'' \<subseteq>\<^sub>m ws" by(rule map_le_trans)
  from redTW_progress_not_Suspend[OF Red, OF t m' wa this ts''ts, of ls']
  obtain ts''' m'''' ws''' obs'''
    where redTW: "redTW t wa (ls', (ts'', m'''), ws'') obs''' (ls', (ts''', m''''), ws''')"
    and m'''': "interrupted_mem_reds ts ws m''' m''''"
    and ws'''ws'': "ws''' \<subseteq>\<^sub>m ws''"
    and ts'''ts: "ts''' |` dom ws''' = ts |` dom ws'''" by blast
  from redTWs redTW have "redTWs t (was @ [wa]) (ls', (ts', m''), ws') (obs @ obs''') (ls', (ts''', m''''), ws''')"
    by(rule redTWs_snocI)
  moreover from ws'''ws'' ws''ws' have "ws''' \<subseteq>\<^sub>m ws'" by(rule map_le_trans)
  moreover from m''' m'''' have "interrupted_mem_reds ts ws m'' m''''" by(rule rtranclp_trans)
  ultimately show ?case using ts'''ts by blast
qed

lemma redTWs_progress:
  assumes Red: "start_state -\<triangleright>tta\<rightarrow>* s"
  and t: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None" "t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
  and cct: "thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "\<exists>obs s'. redTWs t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_upd s t ta x' m') obs s'"
proof -
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s) auto
  { fix t w
    assume "ws t = \<lfloor>w\<rfloor>"
    with preserves_wset_thread_ok[OF Red] s have "ts t \<noteq> None"
      by -(rule notI, auto dest: wset_thread_okD) }
  hence tseq: "thr (redT_upd s t ta x' m') |` dom ws = ts |` dom ws"
    using cct t s by(fastsimp simp add: restrict_map_def expand_fun_eq dest: redT_updTs_Some)
  show ?thesis
  proof(cases "\<exists>w. Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>")
    case False
    hence "\<And>w. Suspend w \<notin> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by simp
    from redTWs_progress_not_Suspend[OF Red[unfolded s], OF t[simplified s thr_conv wset_conv shr_conv] rtranclp.rtrancl_refl this map_le_refl tseq, of "redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"] s
    show ?thesis by(auto simp del: split_paired_Ex)
  next
    case True
    with ta_Suspend_last[OF t(3)] obtain was w
      where was: "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = was @ [Suspend w]"
      and wasSuspend: "\<And>w. Suspend w \<notin> set was"
      by(cases "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" rule: rev_cases) auto
    from redTWs_progress_not_Suspend[OF Red[unfolded s], OF t[simplified s thr_conv wset_conv shr_conv] rtranclp.rtrancl_refl wasSuspend map_le_refl tseq, of "redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"] s
    obtain s' obs where "redTWs t was (redT_upd s t ta x' m') obs s'" by auto
    also obtain s'' where "redTW t (Suspend w) s' [] s''"
      by(fastsimp intro: redTW_Suspend)
    finally (redTWs_snocI) show ?thesis
      unfolding was append_Nil2 by blast
  qed
qed

theorem redT_progress:
  assumes Red: "start_state -\<triangleright>ttas\<rightarrow>* s"
  assumes nfine: "not_final_thread s t"
  and ndead: "\<not> deadlock s"
  shows "\<exists>t' ta' s'. s -t'\<triangleright>ta'\<rightarrow> s'"
proof -
  from ndead
  have "\<exists>t x ln l. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> wset s t = None \<and>
         (ln = no_wait_locks \<and> \<not> final x \<and> (\<exists>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt \<in> LT. \<not> must_wait s t lt t')) \<or>
          ln\<^sub>f l > 0 \<and> (\<forall>l. ln\<^sub>f l > 0 \<longrightarrow> may_lock ((locks s)\<^sub>f l) t))"
    by(rule contrapos_np)(blast intro!: waiting_deadlock[OF Red nfine])
  then obtain t x ln l
    where "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "wset s t = None"
    and a: "(ln = no_wait_locks \<and> \<not> final x \<and> 
             (\<exists>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt \<in> LT. \<not> must_wait s t lt t')) \<or>
             ln\<^sub>f l > 0 \<and> (\<forall>l. ln\<^sub>f l > 0 \<longrightarrow> may_lock ((locks s)\<^sub>f l) t))"
    by blast

  obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by (cases s, auto)
  note conform = wf_red[OF Red, simplified s thr_conv wset_conv shr_conv]
  from `thr s t = \<lfloor>(x, ln)\<rfloor>` have tst: "ts t = \<lfloor>(x, ln)\<rfloor>" by simp
  from s a have a: "(ln = no_wait_locks \<and> \<not> final x \<and> 
            (\<exists>LT. t \<turnstile> \<langle>x, m\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt \<in> LT. \<not> must_wait s t lt t')) \<or>
             ln\<^sub>f l > 0 \<and> (\<forall>l. ln\<^sub>f l > 0 \<longrightarrow> may_lock (ls\<^sub>f l) t))" by simp
  thus ?thesis
  proof(rule disjE)
    assume "ln = no_wait_locks \<and> \<not> final x \<and> (\<exists>LT. t \<turnstile> \<langle>x, m\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt\<in>LT. \<not> must_wait s t lt t'))"
    then obtain LT where [simp]: "ln = no_wait_locks" and nfine': "\<not> final x"
      and cl': "t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>" and mw: "\<And>t' lt. lt\<in>LT \<Longrightarrow> \<not> must_wait s t lt t'"
      by blast
    from `thr s t = \<lfloor>(x, ln)\<rfloor>` nfine'
    obtain x'' m'' ta' where red: "t \<turnstile> \<langle>x, m\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
      by(auto intro: wf_progressE[OF Red])
    from cl'
    have "\<exists>ta''' x''' m'''. t \<turnstile> \<langle>x, m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle> \<and> LT = collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>}"
      by (fastsimp elim!: can_syncE)
    then obtain ta''' x''' m'''
      where red'': "t \<turnstile> \<langle>x, m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle>"
      and L: "LT = collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>}"
      by blast
    from tst[simplified] `wset s t = None`
    obtain ta'' x'' m''
      where red': "t \<turnstile> \<langle>x, m\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
      and cct: "thread_oks ts \<lbrace>ta''\<rbrace>\<^bsub>t\<^esub>"
      and lot: "lock_ok_las' ls t \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
      and collect: "collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub>"
      and cao: "cond_action_oks' (ls, (ts, m), ws) t \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub>"
      and join: "collect_cond_actions \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>"
      by -(rule wf_redE[OF Red, simplified, OF _ red''], auto)

    { fix l
      assume "Inl l \<in> LT"
      hence "\<forall>t'. \<not> must_wait s t (Inl l) t'" by-(rule allI mw)+
      hence "\<forall>t'. t \<noteq> t' \<longrightarrow> \<not> has_lock (ls\<^sub>f l) t'" by(fastsimp)
      hence "may_lock (ls\<^sub>f l) t"
	by-(rule classical, auto simp add: not_may_lock_conv) }
    note mayl = this
    { fix t'
      assume t'LT: "Inr t' \<in> LT"
      hence "\<not> not_final_thread s t' \<and> t' \<noteq> t"
      proof(cases "t' = t")
	case False with t'LT mw L show ?thesis by(auto)
      next
	case True with tst mw[OF t'LT, of t] nfine' L have False
	  by(auto intro!: must_wait.intros simp add: not_final_thread_iff)
	thus ?thesis ..
      qed }
    note mayj = this
    from collect L mayl
    have "\<forall>l\<in>collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>. may_lock (ls\<^sub>f l) t" by auto
    with lot have "\<And>l. l \<in> collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<Longrightarrow> may_lock (ls\<^sub>f l) t"
      by - (rule lock_ok_las'_collect_locks'_may_lock)
    with lot have "lock_ok_las ls t \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
      by -(rule lock_ok_las'_collect_locks_lock_ok_las)
    moreover from cao have "set \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub> \<inter> {Notified, Interrupted} = {}"
      by(auto simp add: cond_action_oks'_subset_Join)
    with mayj join L
    have "cond_action_oks (ls, (ts, m), ws) t \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub>"
      by(fastsimp intro: may_join_cond_action_oks)
    ultimately have "actions_ok s t ta''" using cct by auto
    moreover from redTWs_progress[OF Red, simplified s thr_conv shr_conv wset_conv, OF tst[simplified] _ red' cct]
      `wset s t = None` s
    obtain s' obs where "redTWs t \<lbrace>ta''\<rbrace>\<^bsub>w\<^esub> (redT_upd s t ta'' x'' m'') obs s'" by auto
    ultimately have "s -t\<triangleright>observable_ta_of ta'' obs\<rightarrow> s'" using red' tst `wset s t = None`
      by(auto intro: redT_normal)
    thus ?thesis by blast
  next
    assume "0 < ln\<^sub>f l \<and> (\<forall>l. 0 < ln\<^sub>f l \<longrightarrow> may_lock (ls\<^sub>f l) t)"
    hence "0 < ln\<^sub>f l" "\<And>l. 0 < ln\<^sub>f l \<Longrightarrow> may_lock (ls\<^sub>f l) t" by(auto)
    hence "may_acquire_all ls t ln" by(auto intro: may_acquire_allI)
    with tst `wset s t = None` `0 < ln\<^sub>f l`
    show ?thesis by(fastsimp intro: redT_acquire)
  qed
qed

end

context final_thread_wf begin

lemma lock_thread_ok_must_wait_thread_exists:
  "\<lbrakk> lock_thread_ok (locks s) (thr s); must_wait s t lt t' \<rbrakk> \<Longrightarrow> thr s t' \<noteq> None"
by(auto dest: lock_thread_okD elim!: must_wait_elims)

lemma progress_deadlock:
  assumes wf_progress: "wf_progress final r start_state"
  and wf_red: "wf_red final r start_state"
  shows "progress final r start_state deadlock"
proof(rule progress.intro[OF final_thread_wf_axioms wf_progress wf_red progress_axioms.intro])
  fix ttas s t
  assume Red: "start_state -\<triangleright>ttas\<rightarrow>* s"
    and tst: "not_final_thread s t"
    and normal: "\<And>t x LT. \<lbrakk>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None; t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<rbrakk>
                          \<Longrightarrow> \<exists>t'. \<exists>lt\<in>LT. must_wait s t lt t'"
    and acquire: "\<And>t x ln l. \<lbrakk>thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None; 0 < ln\<^sub>f l\<rbrakk> \<Longrightarrow> \<exists>l'. 0 < ln\<^sub>f l' \<and> \<not> may_lock ((locks s)\<^sub>f l') t"
  have lok: "lock_thread_ok (locks s) (thr s)"
    by(rule multithreaded_start.preserves_lock_thread_ok[OF wf_progress.axioms(1)[OF wf_progress] Red])
  with Red tst normal acquire show "deadlock s"
    by-(rule all_waiting_implies_deadlock,
        (blast dest: lock_thread_ok_must_wait_thread_exists[OF lok]
               intro: must_syncI[OF wf_progress.wf_progress[OF wf_progress]])+)
qed

lemmas progress_deadlocked'_aux = progress_deadlock[unfolded deadlock_eq_deadlocked']
lemmas progress_deadlocked' = progress_deadlocked'_aux

end

end
