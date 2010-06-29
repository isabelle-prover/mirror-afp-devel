(*  Title:      JinjaThreads/Framework/FWProgress.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Progress theorem for the multithreaded semantics} *}

theory FWProgress imports FWDeadlock begin

lemma (in final_thread) lock_thread_ok_must_wait_thread_exists:
  "\<lbrakk> lock_thread_ok (locks s) (thr s); must_wait s t lt t' \<rbrakk> \<Longrightarrow> thr s t' \<noteq> None"
by(auto dest: lock_thread_okD elim!: must_wait_elims)

locale progress = multithreaded_start final r start_state +
  final_thread_wf final r
  for final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80)
  and start_state :: "('l,'t,'x,'m,'w) state" +
  assumes wf_red:
  "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
     t \<turnstile> (x, shr s) -ta\<rightarrow> (x', m'); \<not> waiting (wset s t) \<rbrakk>
  \<Longrightarrow> \<exists>ta' x' m'. t \<turnstile> (x, shr s) -ta'\<rightarrow> (x', m') \<and> actions_ok' s t ta' \<and> actions_subset ta' ta"

  and red_wait_set_not_final:
  "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; wset s t = \<lfloor>WokenUp w\<rfloor> \<rbrakk> \<Longrightarrow> \<not> final x"

  and wf_progress:
  "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> final x \<rbrakk>
  \<Longrightarrow> \<exists>ta x' m'. t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
begin

lemma wf_redE:
  assumes "start_state -\<triangleright>ttas\<rightarrow>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
  and "t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>" "\<not> waiting (wset s t)"
  obtains ta' x' m'
  where "t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>" "actions_ok' s t ta'" "actions_subset ta' ta"
using assms
by(blast dest: wf_red)

lemma wf_redE':
  assumes "start_state -\<triangleright>ttas\<rightarrow>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>" "\<not> waiting (wset s t)"
  obtains ta' x' m'
  where "t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>" "thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>"
  and "lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>" "collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  and "cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>"
  and "collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
using assms
by(blast dest: wf_red)

lemma wf_progressE:
  assumes "start_state -\<triangleright>tta\<rightarrow>* s"
  and "thr s t = \<lfloor>(x, ln)\<rfloor>" "\<not> final x"
  obtains ta x' m' where "t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
using assms
by(blast dest: wf_progress)

theorem redT_progress:
  assumes Red: "start_state -\<triangleright>ttas\<rightarrow>* s"
  assumes nfine: "not_final_thread s t"
  and ndead: "\<not> deadlock s"
  shows "\<exists>t' ta' s'. s -t'\<triangleright>ta'\<rightarrow> s'"
proof -
  from Red have lok: "lock_thread_ok (locks s) (thr s)"
    by(rule preserves_lock_thread_ok)
  from ndead
  have "\<exists>t x ln l. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> 
          (wset s t = None \<and> ln = no_wait_locks \<and> \<not> final x \<and> (\<exists>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt \<in> LT. \<not> must_wait s t lt t')) \<or>
           \<not> waiting (wset s t) \<and> ln\<^sub>f l > 0 \<and> (\<forall>l. ln\<^sub>f l > 0 \<longrightarrow> may_lock ((locks s)\<^sub>f l) t) \<or>
          (\<exists>w. ln = no_wait_locks \<and> wset s t = \<lfloor>WokenUp w\<rfloor>))"
    by(rule contrapos_np)(blast intro!: all_waiting_implies_deadlock[OF nfine lok] dest: lock_thread_ok_must_wait_thread_exists[OF lok] intro: must_syncI[OF wf_progress[OF Red]])
  then obtain t x ln l
    where "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and a: "wset s t = None \<and> ln = no_wait_locks \<and> \<not> final x \<and> 
              (\<exists>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt \<in> LT. \<not> must_wait s t lt t')) \<or>
            \<not> waiting (wset s t) \<and> ln\<^sub>f l > 0 \<and> (\<forall>l. ln\<^sub>f l > 0 \<longrightarrow> may_lock ((locks s)\<^sub>f l) t) \<or>
            (\<exists>w. ln = no_wait_locks \<and> wset s t = \<lfloor>WokenUp w\<rfloor>)"
    by blast

  obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by (cases s) auto
  note conform = wf_red[OF Red, unfolded s thr_conv wset_conv shr_conv]
  from `thr s t = \<lfloor>(x, ln)\<rfloor>` have tst: "ts t = \<lfloor>(x, ln)\<rfloor>" by simp
  from s a have cases[case_names normal acquire wakeup]:
    "\<And>thesis. 
        \<lbrakk> \<And>LT. \<lbrakk> ws t = None; ln = no_wait_locks; \<not> final x; t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>; 
                 \<And>t' lt. lt \<in> LT \<Longrightarrow> \<not> must_wait s t lt t' \<rbrakk> \<Longrightarrow> thesis;
          \<lbrakk> \<not> waiting (ws t); ln\<^sub>f l > 0; \<And>l. ln\<^sub>f l > 0 \<Longrightarrow> may_lock (ls\<^sub>f l) t \<rbrakk> \<Longrightarrow> thesis;
          \<And>w. \<lbrakk> ln = no_wait_locks; ws t = \<lfloor>WokenUp w\<rfloor> \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
    by auto
  show ?thesis
  proof(cases rule: cases)
    case (normal LT)
    note [simp] = `ln = no_wait_locks` 
      and nfine' = `\<not> final x`
      and cl' = `t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>` 
      and mw = `\<And>t' lt. lt\<in>LT \<Longrightarrow> \<not> must_wait s t lt t'`
    from tst nfine' obtain x'' m'' ta'
      where red: "t \<turnstile> \<langle>x, m\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
      by(auto intro: wf_progressE[OF Red])
    from cl'
    have "\<exists>ta''' x''' m'''. t \<turnstile> \<langle>x, m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle> \<and> LT = collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>}"
      by (fastsimp elim!: can_syncE)
    then obtain ta''' x''' m'''
      where red'': "t \<turnstile> \<langle>x, m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle>"
      and L: "LT = collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>}"
      by blast
    from `ws t = None` have "\<not> waiting (ws t)" by(simp add: not_waiting_iff)
    with tst[simplified]
    obtain ta'' x'' m''
      where red': "t \<turnstile> \<langle>x, m\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
      and cct: "thread_oks ts \<lbrace>ta''\<rbrace>\<^bsub>t\<^esub>"
      and lot: "lock_ok_las' ls t \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
      and collect: "collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub>"
      and cao: "cond_action_oks' (ls, (ts, m), ws) t \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub>"
      and join: "collect_cond_actions \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>"
      and wao: "wset_actions_ok ws t \<lbrace>ta''\<rbrace>\<^bsub>w\<^esub>"
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
    have "\<And>l. l \<in> collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<Longrightarrow> may_lock (ls\<^sub>f l) t" by auto
    with lot have "lock_ok_las ls t \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>" by(rule lock_ok_las'_into_lock_on_las)
    moreover
    from mayj join L
    have "cond_action_oks (ls, (ts, m), ws) t \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub>"
      by(fastsimp intro: may_join_cond_action_oks)
    ultimately have "actions_ok s t ta''" using cct wao by auto
    hence "s -t\<triangleright>observable_ta_of ta''\<rightarrow> redT_upd s t ta'' x'' m''"
      using red' tst `ws t = None`
      by(auto intro: redT_normal)
    thus ?thesis by blast
  next
    case acquire
    hence "may_acquire_all ls t ln" by(auto intro: may_acquire_allI)
    with tst `\<not> waiting (ws t)` `0 < ln\<^sub>f l`
    show ?thesis by(fastsimp intro: redT_acquire)
  next
    case (wakeup w)
    from `ws t = \<lfloor>WokenUp w\<rfloor>`
    have "\<not> waiting (wset s t)" by(simp add: not_waiting_iff)
    from red_wait_set_not_final[OF Red, of t x w] tst wakeup
    have "\<not> final x" by simp
    from wf_progress[OF Red _ this, of t ln] tst
    obtain ta x' m' where red: "t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>" by auto
    from tst wakeup have "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" by simp
    with Red obtain ta' x'' m'' 
      where red': "t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
      and aok': "actions_ok' s t ta'"
      and subset: "actions_subset ta' ta"
      using red `\<not> waiting (wset s t)` by(rule wf_redE)
    from wakeup aok' have "Notified \<in> set \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> \<or> Interrupted \<in> set \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>"
      by(auto simp add: wset_actions_ok_def split: split_if_asm)
    from ta_Wakeup_no_join_no_lock[OF red' this]
    have no_join: "\<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = []" and no_lock: "collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = {}" by auto
    from no_lock have no_lock': "collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = {}"
      using collect_locks'_subset_collect_locks[of "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>"] by auto
    from aok' have "lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>" by auto
    hence "lock_ok_las (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>"
      by(rule lock_ok_las'_into_lock_on_las)(simp add: no_lock')
    moreover from subset aok' no_join have "cond_action_oks s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>"
      by(auto intro: may_join_cond_action_oks)
    ultimately have "actions_ok s t ta'" using aok' by auto
    with tst red' wakeup have "s -t\<triangleright>observable_ta_of ta'\<rightarrow> redT_upd s t ta' x'' m''"
      by(auto intro: redT_normal)
    thus ?thesis by blast
  qed
qed

theorem redT_progress_deadlocked':
  "\<lbrakk> start_state -\<triangleright>ttas\<rightarrow>* s; not_final_thread s t; \<not> deadlocked' s \<rbrakk>
  \<Longrightarrow> \<exists>t' ta' s'. s -t'\<triangleright>ta'\<rightarrow> s'"
unfolding deadlock_eq_deadlocked'[symmetric]
by(rule redT_progress)

end

end
