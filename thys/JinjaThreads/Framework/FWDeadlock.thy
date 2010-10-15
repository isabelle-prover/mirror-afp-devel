(*  Title:      JinjaThreads/Framework/FWDeadlock.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Deadlock formalisation} *}

theory FWDeadlock imports FWProgressAux begin

context final_thread begin

inductive must_wait :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l + 't) \<Rightarrow> 't \<Rightarrow> bool"
  for s :: "('l,'t,'x,'m,'w) state" and t :: "'t" where
  "\<lbrakk> has_lock ((locks s)\<^sub>f l) t'; t' \<noteq> t \<rbrakk> \<Longrightarrow> must_wait s t (Inl l) t'"
| "not_final_thread s t' \<Longrightarrow> must_wait s t (Inr t') t'"

declare must_wait.cases [elim]
declare must_wait.intros [intro]

lemma must_wait_elims [consumes 1, case_names lock thread, cases pred]:
  "\<lbrakk> must_wait s t lt t'; \<And>l. \<lbrakk>lt = Inl l; 
     has_lock ((locks s)\<^sub>f l) t'; t' \<noteq> t\<rbrakk> \<Longrightarrow> thesis;
     \<lbrakk>lt = Inr t'; not_final_thread s t'\<rbrakk> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
by(auto)

inductive_cases must_wait_elims2 [elim!]:
  "must_wait s t (Inl l) t'"
  "must_wait s t (Inr t'') t'"

lemma must_wait_iff:
  "must_wait s t lt t' \<longleftrightarrow> (case lt of Inl l \<Rightarrow> t \<noteq> t' \<and> has_lock ((locks s)\<^sub>f l) t'
                                    | Inr t'' \<Rightarrow> t' = t'' \<and> not_final_thread s t'')"
by(cases lt)(auto)

end

text{* Deadlock as a system-wide property *}

context multithreaded_base begin

definition
  deadlock :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where
  "deadlock s
   \<equiv> (\<exists>t. not_final_thread s t)
     \<and> (\<forall>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> \<not> final x \<and> wset s t = None
        \<longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t'))))
     \<and> (\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<exists>l. ln\<^sub>f l > 0) \<and> \<not> waiting (wset s t)
        \<longrightarrow> (\<exists>l t'. ln\<^sub>f l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t'))
     \<and> (\<forall>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> wset s t \<noteq> \<lfloor>WokenUp w\<rfloor>)"

lemma deadlockI:
  "\<lbrakk> not_final_thread s t;
    \<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk>
    \<Longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t')));
    \<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ln\<^sub>f l > 0; \<not> waiting (wset s t) \<rbrakk>
    \<Longrightarrow> \<exists>l t'. ln\<^sub>f l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t';
    \<And>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<Longrightarrow> wset s t \<noteq> \<lfloor>WokenUp w\<rfloor> \<rbrakk>
  \<Longrightarrow> deadlock s"
by(auto simp add: deadlock_def)

lemma deadlockE:
  assumes "deadlock s"
  obtains t ln x w
  where "thr s t = \<lfloor>(x, ln)\<rfloor>"
  and "not_final_thread s t"
  and "\<forall>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> \<not> final x \<and> wset s t = None
        \<longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t')))"
  and "\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<exists>l. ln\<^sub>f l > 0) \<and> \<not> waiting (wset s t)
                \<longrightarrow> (\<exists>l t'. ln\<^sub>f l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t')"
  and "\<forall>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> wset s t \<noteq> \<lfloor>WokenUp w\<rfloor>"
using assms unfolding deadlock_def by(blast)

lemma deadlockD1:
  assumes "deadlock s"
  and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
  and "\<not> final x"
  and "wset s t = None"
  obtains "t \<turnstile> \<langle>x, shr s\<rangle> \<wrong>"
  and "\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t'))"
using assms unfolding deadlock_def by(blast)

lemma deadlockD2:
  assumes "deadlock s"
  and "thr s t = \<lfloor>(x, ln)\<rfloor>"
  and "ln\<^sub>f l > 0"
  and "\<not> waiting (wset s t)"
  obtains l' t' where "ln\<^sub>f l' > 0" "t \<noteq> t'" "thr s t' \<noteq> None" "has_lock ((locks s)\<^sub>f l') t'"
using assms unfolding deadlock_def by blast

lemma deadlockD3:
  assumes "deadlock s"
  and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
  shows "\<forall>w. wset s t \<noteq> \<lfloor>WokenUp w\<rfloor>"
using assms unfolding deadlock_def by blast

lemma all_waiting_implies_deadlock:
  assumes "not_final_thread s t"
  and "lock_thread_ok (locks s) (thr s)"
  and normal: "\<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk> 
               \<Longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t')))"
  and acquire: "\<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); ln\<^sub>f l > 0 \<rbrakk>
                 \<Longrightarrow> \<exists>l'. ln\<^sub>f l' > 0 \<and> \<not> may_lock ((locks s)\<^sub>f l') t"
  and wakeup: "\<And>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<Longrightarrow> wset s t \<noteq> \<lfloor>WokenUp w\<rfloor>"
  shows "deadlock s"
proof(rule deadlockI)
  from `not_final_thread s t` show "not_final_thread s t" .
next
  fix T X
  assume tsT: "thr s T = \<lfloor>(X, no_wait_locks)\<rfloor>"
    and "\<not> final X" 
    and "wset s T = None"
  show "T \<turnstile> \<langle>X, shr s\<rangle> \<wrong> \<and> (\<forall>LT. T \<turnstile> \<langle>X, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. must_wait s T lt t')))"
    by(rule normal[OF tsT `\<not> final X` `wset s T = None`])
next
  fix T X LN l'
  assume "thr s T = \<lfloor>(X, LN)\<rfloor>"
    and "0 < LN\<^sub>f l'"
    and wset: "\<not> waiting (wset s T)"
  from acquire[OF `thr s T = \<lfloor>(X, LN)\<rfloor>` wset, OF `0 < LN\<^sub>f l'`]
  obtain l' where "0 < LN\<^sub>f l'" "\<not> may_lock ((locks s)\<^sub>f l') T" by blast
  then obtain t' where "T \<noteq> t'" "has_lock ((locks s)\<^sub>f l') t'"
    unfolding not_may_lock_conv by fastsimp
  moreover with `lock_thread_ok (locks s) (thr s)`
  have "thr s t' \<noteq> None" by(auto dest: lock_thread_okD)
  ultimately show "\<exists>l t'. 0 < LN\<^sub>f l \<and> T \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t'"
    using `0 < LN\<^sub>f l'` by(auto)
qed(rule wakeup)

end

text {* Now deadlock for single threads *}

context final_thread begin

definition all_final_except :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> bool" where
  "all_final_except s P \<equiv> \<forall>t. not_final_thread s t \<longrightarrow> P t"

lemma all_final_except_mono [mono]:
  "(\<And>x. A x \<longrightarrow> B x) \<Longrightarrow> all_final_except ts A \<longrightarrow> all_final_except ts B"
by(auto simp add: all_final_except_def)

lemma all_final_except_mono':
  "\<lbrakk> all_final_except ts A; \<And>x. A x \<Longrightarrow> B x \<rbrakk> \<Longrightarrow> all_final_except ts B"
by(blast intro: all_final_except_mono[rule_format])

lemma all_final_exceptI:
  "(\<And>t. not_final_thread s t \<Longrightarrow> P t) \<Longrightarrow> all_final_except s P"
by(auto simp add: all_final_except_def)

lemma all_final_exceptD:
  "\<lbrakk> all_final_except s P; not_final_thread s t \<rbrakk> \<Longrightarrow> P t"
by(auto simp add: all_final_except_def)

end

context multithreaded_base begin

coinductive deadlocked :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool"
  for s :: "('l,'t,'x,'m,'w) state" where
  deadlockedLock:
    "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> \<langle>x, shr s\<rangle> \<wrong>; wset s t = None;
       \<And>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s t lt t') \<rbrakk>
     \<Longrightarrow> deadlocked s t"

| deadlockedWait:
    "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; all_final_except s (deadlocked s); waiting (wset s t) \<rbrakk> \<Longrightarrow> deadlocked s t"

| deadlockedAcquire:
    "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); ln\<^sub>f l > 0; has_lock ((locks s)\<^sub>f l) t'; t' \<noteq> t; 
       deadlocked s t' \<or> final_thread s t' \<rbrakk> 
     \<Longrightarrow> deadlocked s t"

lemma deadlocked_elims [consumes 1, case_names lock wait acquire]:
  assumes "deadlocked s t"
  and lock: "\<And>x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> \<langle>x, shr s\<rangle> \<wrong>; wset s t = None;
                   \<And>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s t lt t') \<rbrakk>
             \<Longrightarrow> thesis"
  and wait: "\<And>x ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; all_final_except s (deadlocked s); waiting (wset s t) \<rbrakk> \<Longrightarrow> thesis"
  and acquire: "\<And>x ln l t'. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); 0 < ln\<^sub>f l; has_lock ((locks s)\<^sub>f l) t'; t \<noteq> t';
                              deadlocked s t' \<or> final_thread s t' \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
using `deadlocked s t`
apply(rule deadlocked.cases)
apply(rule lock, blast+)
apply(rule wait, blast+)
apply(rule acquire, blast+)
done

definition deadlocked' :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool" where
  "deadlocked' s \<equiv> (\<exists>t. not_final_thread s t) \<and> (\<forall>t. not_final_thread s t \<longrightarrow> deadlocked s t)"

lemma deadlocked'I:
  "\<lbrakk> not_final_thread s t; \<And>t. not_final_thread s t \<Longrightarrow> deadlocked s t \<rbrakk> \<Longrightarrow> deadlocked' s"
by(auto simp add: deadlocked'_def)

lemma deadlocked'D1E:
  "\<lbrakk> deadlocked' s; \<And>t. not_final_thread s t \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto simp add: deadlocked'_def)

lemma deadlocked'D2:
  "\<lbrakk> deadlocked' s; not_final_thread s t; deadlocked s t \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto simp add: deadlocked'_def)

lemma not_deadlocked'I:
  "\<lbrakk> not_final_thread s t; \<not> deadlocked s t \<rbrakk> \<Longrightarrow> \<not> deadlocked' s"
by(auto dest: deadlocked'D2)

lemma deadlocked'_intro:
  "\<lbrakk> not_final_thread s t; \<forall>t. not_final_thread s t \<longrightarrow> deadlocked s t \<rbrakk> \<Longrightarrow> deadlocked' s"
by(rule deadlocked'I)(blast)+

lemma deadlocked_thread_exists: 
  assumes "deadlocked s t"
  obtains x ln where "thr s t = \<lfloor>(x, ln)\<rfloor>"
using assms
by(blast elim: deadlocked.cases)

end

context final_thread_wf begin 

lemma red_no_deadlock: 
  assumes P: "s -t\<triangleright>ta\<rightarrow> s'"
  and dead: "deadlocked s t"
  shows False
proof -
  obtain las tas cas was obs where ta: "ta = (las, tas, cas, was, obs)" by(cases ta)
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by (cases s, auto)
  obtain ls' ts' m' ws' where s': "s' = (ls', (ts', m'), ws')" by (cases s', auto)
  with P s have "\<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>" by simp
  thus False
  proof(cases rule: redT_elims)
    case (normal x x' M')
    with ta have Pe: "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', M'\<rangle>"
      and est: "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and lot: "lock_ok_las ls t las"
      and cct: "thread_oks ts tas"
      and cdt: "cond_action_oks (ls, (ts, m), ws) t cas"
      and wao: "wset_actions_ok ws t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
      by(auto)
    show False
    proof(cases "all_final_except s (deadlocked s) \<and> (\<exists>w. ws t = \<lfloor>InWS w\<rfloor>)")
      case True with wao show ?thesis by(auto simp add: wset_actions_ok_def split: split_if_asm)
    next
      case False
      with dead est s
      have mle: "t \<turnstile> \<langle>x, m\<rangle> \<wrong>"
	and cledead: "\<forall>LT. t \<turnstile> \<langle>x, m\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s t lt t'))"
	by - (erule deadlocked.cases, (fastsimp simp add: waiting_def)+)+
      let ?LT = "collect_locks las <+> {t. Join t \<in> set cas}"
      from Pe ta have "t \<turnstile> \<langle>x, m\<rangle> ?LT \<wrong>" by(auto intro: can_syncI)
      then obtain t' lt where "deadlocked s t' \<or> final_thread s t'"
	and lt: "lt \<in> ?LT" and mw: "must_wait s t lt t'"
	by(blast dest: cledead[rule_format])
      from mw show False
      proof(cases rule: must_wait_elims)
	case (lock l)
	from `lt = Inl l` lt have "l \<in> collect_locks las" by(auto)
	with lot have "may_lock (ls\<^sub>f l) t"
	  by(auto elim!: collect_locksE lock_ok_las_may_lock)
	with `has_lock ((locks s)\<^sub>f l) t'` s have "t' = t"
	  by(auto dest: has_lock_may_lock_t_eq)
	with `t' \<noteq> t` show False by contradiction
      next
	case thread
	from `lt = Inr t'` lt have "Join t' \<in> set cas" by auto
	from `not_final_thread s t'`  obtain x'' ln''
	  where "thr s t' = \<lfloor>(x'', ln'')\<rfloor>" by(rule not_final_thread_existsE)
	moreover with `Join t' \<in> set cas` cdt s
	have "final x''" "ln'' = no_wait_locks" "ws t' = None"
	  by(auto dest: cond_action_oks_Join)
	ultimately show False using `not_final_thread s t'` s by(auto)
      qed
    qed
  next
    case (acquire x ln n)
    hence "\<not> waiting (ws t)" and "ts t = \<lfloor>(x, ln)\<rfloor>" 
      and "may_acquire_all ls t ln" by auto
    show False
    proof(cases "all_final_except s (deadlocked s) \<and> (\<exists>w. ws t = \<lfloor>InWS w\<rfloor>)")
      case True with `\<not> waiting (ws t)` show ?thesis
        by(auto simp add: not_waiting_iff)
    next
      case False
      with dead `ts t = \<lfloor>(x, ln)\<rfloor>` `0 < ln\<^sub>f n` s
      obtain l t' where "0 < ln\<^sub>f l" "t \<noteq> t'"
	and "has_lock (ls\<^sub>f l) t'"
	by  -(erule deadlocked.cases, (fastsimp simp add: waiting_def)+)
      hence "\<not> may_acquire_all ls t ln"
	by(auto elim: may_acquire_allE dest: has_lock_may_lock_t_eq)
      with `may_acquire_all ls t ln` show ?thesis by contradiction
    qed
  qed
qed

lemma deadlocked'_no_red:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; deadlocked' s \<rbrakk> \<Longrightarrow> False"
apply(rule red_no_deadlock)
 apply(assumption)
apply(erule deadlocked'D2)
by(rule red_not_final_thread)


lemma not_final_thread_deadlocked_final_thread [simp, iff]: 
  "thr s t = \<lfloor>xln\<rfloor> \<Longrightarrow> not_final_thread s t \<or> deadlocked s t \<or> final_thread s t"
by(auto simp add: not_final_thread_final_thread_conv[symmetric])


lemma all_waiting_deadlocked:
  assumes "not_final_thread s t"
  and "lock_thread_ok (locks s) (thr s)" 
  and normal: "\<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk> 
               \<Longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. must_wait s t lt t')))"
  and acquire: "\<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); ln\<^sub>f l > 0 \<rbrakk>
                \<Longrightarrow> \<exists>l'. ln\<^sub>f l' > 0 \<and> \<not> may_lock ((locks s)\<^sub>f l') t"
  and wakeup: "\<And>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<Longrightarrow> wset s t \<noteq> \<lfloor>WokenUp w\<rfloor>"
  shows "deadlocked s t"
proof -
  obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)"
    by (cases s, auto)
  from `not_final_thread s t` show ?thesis
  proof(coinduct)
    case (deadlocked z)
    then obtain x' ln' where "thr s z = \<lfloor>(x', ln')\<rfloor>" by(fastsimp elim!: not_final_thread_existsE)
    hence "ts z = \<lfloor>(x', ln')\<rfloor>" by simp
    { assume "ws z = None" "\<not> final x'"
      and [simp]: "ln' = no_wait_locks"
      with `ts z = \<lfloor>(x', ln')\<rfloor>`
      have "z \<turnstile> \<langle>x', m\<rangle> \<wrong> \<and> (\<forall>LT. z \<turnstile> \<langle>x', m\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s z lt t')))"
	by(auto dest: normal[simplified])
      then obtain "z \<turnstile> \<langle>x', m\<rangle> \<wrong>"
	and clnml: "\<And>LT. z \<turnstile> \<langle>x', m\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s z lt t')" by(blast)
      { fix LT
	assume "z \<turnstile> \<langle>x', m\<rangle> LT \<wrong>"
	then obtain t' where "thr s t' \<noteq> None" "\<exists>lt \<in> LT. must_wait s z lt t'"
	  by(blast dest: clnml)
	from `thr s t' \<noteq> None` obtain xln where "thr s t' = \<lfloor>xln\<rfloor>" by auto
	hence "not_final_thread s t' \<or> deadlocked s t' \<or> final_thread s t'"
	  by(rule not_final_thread_deadlocked_final_thread)
	with `\<exists>lt \<in> LT. must_wait s z lt t'`
	have "\<exists>t'. (not_final_thread s t' \<or> deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s z lt t')"
	  by blast }
      with `z \<turnstile> \<langle>x', m\<rangle> \<wrong>` `ts z = \<lfloor>(x', ln')\<rfloor>` `ws z = None` have ?case by(simp) }
    note c1 = this
    { assume wsz: "\<not> waiting (ws z)"
      and "ln' \<noteq> no_wait_locks"
      from `ln' \<noteq> no_wait_locks` obtain l where "0 < ln'\<^sub>f l"
	by(auto simp add: neq_no_wait_locks_conv)
      with wsz `ts z = \<lfloor>(x', ln')\<rfloor>` 
      obtain l' where "0 < ln'\<^sub>f l'" "\<not> may_lock (ls\<^sub>f l') z"
	by(blast dest: acquire[simplified])
      then obtain t'' where "t'' \<noteq> z" "has_lock (ls\<^sub>f l') t''"
	unfolding not_may_lock_conv by blast
      with `lock_thread_ok (locks s) (thr s)`
      obtain x'' ln'' where "ts t'' = \<lfloor>(x'', ln'')\<rfloor>"
	by(auto elim!: lock_thread_ok_has_lockE)
      hence "(not_final_thread s t'' \<or> deadlocked s t'') \<or> final_thread s t''"
	by(clarsimp simp add: not_final_thread_iff final_thread_def)
      with wsz `0 < ln'\<^sub>f l'` `ts z = \<lfloor>(x', ln')\<rfloor>` `t'' \<noteq> z` `has_lock (ls\<^sub>f l') t''`
      have ?deadlockedAcquire by simp blast
      hence ?case by simp }
    note c2 = this
    { fix w
      assume "waiting (ws z)"
      with `ts z = \<lfloor>(x', ln')\<rfloor>` s
      have "?deadlockedWait" by(clarsimp simp add: all_final_except_def)
      hence ?case by simp }
    note c3 = this
    from `not_final_thread s z` `thr s z = \<lfloor>(x', ln')\<rfloor>` show ?case
    proof(cases rule: not_final_thread_cases2)
      case final show ?thesis
      proof(cases "ws z")
        case None show ?thesis
	proof(cases "ln' = no_wait_locks")
	  case True with None final show ?thesis by(rule c1)
	next
	  case False
          from None have "\<not> waiting (ws z)" by(simp add: not_waiting_iff)
          thus ?thesis using False by(rule c2)
	qed
      next
	case (Some w)
        show ?thesis
        proof(cases w)
          case (InWS w') 
          with Some have "waiting (ws z)" by(simp add: waiting_def)
          thus ?thesis by(rule c3)
        next
          case (WokenUp w')
          with Some have "\<not> waiting (ws z)" by(simp add: not_waiting_iff)
          moreover from WokenUp `thr s z = \<lfloor>(x', ln')\<rfloor>` Some
          have "ln' \<noteq> no_wait_locks" by(auto dest: wakeup[simplified])
          ultimately show ?thesis by(rule c2)
        qed
      qed
    next
      case wait_locks show ?thesis
      proof(cases "ws z")
	case None
        hence "\<not> waiting (ws z)" by(simp add: not_waiting_iff)
        thus ?thesis using wait_locks by(rule c2)
      next
	case (Some w)
        show ?thesis
        proof(cases w)
          case (InWS w')
          with Some have "waiting (ws z)" by(simp add: waiting_def)
          thus ?thesis by(rule c3)
        next
          case (WokenUp w')
          with Some have "\<not> waiting (ws z)" by(simp add: not_waiting_iff)
          moreover from WokenUp `thr s z = \<lfloor>(x', ln')\<rfloor>` Some
          have "ln' \<noteq> no_wait_locks" by(auto dest: wakeup[simplified])
          ultimately show ?thesis by(rule c2)
        qed
      qed
    next
      case (wait_set w)
      show ?thesis
      proof(cases w)
        case (InWS w')
        with wait_set have "waiting (ws z)" by(simp add: waiting_def)
        thus ?thesis by(rule c3)
      next
        case (WokenUp w')
        with wait_set have "\<not> waiting (ws z)" by(simp add: not_waiting_iff)
        moreover from WokenUp `thr s z = \<lfloor>(x', ln')\<rfloor>` wait_set
        have "ln' \<noteq> no_wait_locks" by(auto dest: wakeup[simplified])
        ultimately show ?thesis by(rule c2)
      qed
    qed
  qed
qed

text {* Equivalence proof for both notions of deadlock *}

lemma deadlock_implies_deadlocked':
  assumes dead: "deadlock s" 
  shows "deadlocked' s"
proof -
  from dead obtain TT where "not_final_thread s TT" by(rule deadlockE)
  thus ?thesis
  proof(rule deadlocked'I)
    fix t
    assume "not_final_thread s t"
    thus "deadlocked s t"
    proof(coinduct)
      case (deadlocked t'')
      then obtain x'' ln'' where tst'': "thr s t'' = \<lfloor>(x'', ln'')\<rfloor>"
	by(rule not_final_thread_existsE)
      { assume "waiting (wset s t'')"
	moreover
	with tst'' have nfine: "not_final_thread s t''"
          unfolding waiting_def
	  by(blast intro: not_final_thread.intros)
	ultimately have ?case using tst''
	  by(blast intro: all_final_exceptI not_final_thread_final) }
      note c1 = this
      { 
        assume wst'': "\<not> waiting (wset s t'')"
	  and "ln'' \<noteq> no_wait_locks"
	then obtain l where l: "ln''\<^sub>f l > 0"
	  by(auto simp add: neq_no_wait_locks_conv)
	with dead wst'' tst'' obtain l' T
	  where "ln''\<^sub>f l' > 0" "t'' \<noteq> T" 
	  and hl: "has_lock ((locks s)\<^sub>f l') T"
	  and tsT: "thr s T \<noteq> None"
	  by - (erule deadlockD2)
	moreover from `thr s T \<noteq> None`
	obtain xln where tsT: "thr s T = \<lfloor>xln\<rfloor>" by auto
	then obtain X LN where "thr s T = \<lfloor>(X, LN)\<rfloor>"
	  by(cases xln, auto)
	moreover hence "not_final_thread s T \<or> final_thread s T"
	  by(auto simp add: final_thread_def not_final_thread_iff)
	ultimately have ?case using wst'' tst'' by blast }
      note c2 = this
      { assume "wset s t'' = None"
	and [simp]: "ln'' = no_wait_locks"
	moreover
	with `not_final_thread s t''` tst''
	have "\<not> final x''" by(auto)
	ultimately obtain "t'' \<turnstile> \<langle>x'', shr s\<rangle> \<wrong>"
	  and clnml: "\<And>LT. t'' \<turnstile> \<langle>x'', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. must_wait s t'' lt t')"
	  using `thr s t'' = \<lfloor>(x'', ln'')\<rfloor>` `deadlock s`
	  by(blast elim: deadlockD1)
	{ fix LT
	  assume "t'' \<turnstile> \<langle>x'', shr s\<rangle> LT \<wrong>"
	  then obtain t' where "thr s t' \<noteq> None"
	    and mw: "\<exists>lt\<in>LT. must_wait s t'' lt t'" by(blast dest: clnml)
	  from `thr s t' \<noteq> None` have "not_final_thread s t' \<or> final_thread s t'"
	    by(auto simp add: final_thread_def not_final_thread_iff)
	  with mw have "\<exists>t'.(not_final_thread s t' \<or> deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt\<in>LT. must_wait s t'' lt t')"
	    by fastsimp }
	with `t'' \<turnstile> \<langle>x'', shr s\<rangle> \<wrong>` tst'' `wset s t'' = None` have ?case by(simp) }
      note c3 = this
      from `not_final_thread s t''` tst'' show ?case
      proof(cases rule: not_final_thread_cases2)
	case final show ?thesis
	proof(cases "wset s t''")
	  case None show ?thesis
	  proof(cases "ln'' = no_wait_locks")
	    case True with None show ?thesis by(rule c3)
	  next
	    case False
            from None have "\<not> waiting (wset s t'')" by(simp add: not_waiting_iff)
            thus ?thesis using False by(rule c2)
	  qed
	next
	  case (Some w)
          show ?thesis
          proof(cases w)
            case (InWS w')
            with Some have "waiting (wset s t'')" by(simp add: waiting_def)
            thus ?thesis by(rule c1)
          next
            case (WokenUp w')
            hence "\<not> waiting (wset s t'')" using Some by(simp add: not_waiting_iff)
            moreover from WokenUp Some tst''
            have "ln'' \<noteq> no_wait_locks" by(auto dest: deadlockD3[OF dead])
            ultimately show ?thesis by(rule c2)
          qed            
	qed
      next
	case wait_locks show ?thesis
	proof(cases "waiting (wset s t'')")
          case False
          thus ?thesis using wait_locks by(rule c2)
        next
          case True thus ?thesis by(rule c1)
        qed
      next
	case (wait_set w)
        show ?thesis
        proof(cases w)
          case InWS
          with wait_set have "waiting (wset s t'')" by(simp add: waiting_def)
          thus ?thesis by(rule c1)
        next
          case (WokenUp w')
          hence "\<not> waiting (wset s t'')" using wait_set
            by(simp add: not_waiting_iff)
          moreover from WokenUp wait_set tst''
          have "ln'' \<noteq> no_wait_locks" by(auto dest: deadlockD3[OF dead])
          ultimately show ?thesis by(rule c2)
        qed
      qed
    qed
  qed
qed


lemma deadlocked'_implies_deadlock:
  assumes dead: "deadlocked' s" 
  shows "deadlock s"
proof -
  from dead obtain TT where "not_final_thread s TT"
    by(rule deadlocked'D1E)
  have deadlocked: "\<And>t. not_final_thread s t \<Longrightarrow> deadlocked s t"
    using dead by(rule deadlocked'D2)
  show ?thesis
  proof(rule deadlockI)
    from `not_final_thread s TT` show "not_final_thread s TT" .
  next
    fix t' x'
    assume "thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>"
      and "\<not> final x'"
      and "wset s t' = None"
    hence "not_final_thread s t'" by(auto intro: not_final_thread_final)
    hence "deadlocked s t'" by(rule deadlocked)
    thus "t' \<turnstile> \<langle>x', shr s\<rangle> \<wrong> \<and> (\<forall>LT. t' \<turnstile> \<langle>x', shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t''. thr s t'' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t' lt t'')))"
    proof(cases rule: deadlocked_elims)
      case (lock x'')
      hence lock: "\<And>LT. t' \<turnstile> \<langle>x'', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>T. (deadlocked s T \<or> final_thread s T) \<and> (\<exists>lt \<in> LT. must_wait s t' lt T)"
	by blast
      from `thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>` `thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>`
      have [simp]: "x' = x''" by auto
      have "\<And>LT. t' \<turnstile> \<langle>x'', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t''. thr s t'' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t' lt t'')"
	by -(drule lock, auto elim!: deadlocked_thread_exists final_threadE)
      with `t' \<turnstile> \<langle>x'', shr s\<rangle> \<wrong>` show ?thesis by(auto)
    next
      case (wait x'' ln'')
      from `wset s t' = None` `waiting (wset s t')`
      have False by(simp add: waiting_def)
      thus ?thesis ..
    next
      case (acquire x'' ln'' l'' T)
      from `thr s t' = \<lfloor>(x'', ln'')\<rfloor>` `thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>` `0 < ln''\<^sub>f l''`
      have False by(auto)
      thus ?thesis ..
    qed
  next
    fix t' x' ln' l
    assume "thr s t' = \<lfloor>(x', ln')\<rfloor>"
      and "0 < ln'\<^sub>f l"
      and wst': "\<not> waiting (wset s t')"
    hence "not_final_thread s t'" by(auto intro: not_final_thread_wait_locks)
    hence "deadlocked s t'" by(rule deadlocked)
    thus "\<exists>l T. 0 < ln'\<^sub>f l \<and> t' \<noteq> T \<and> thr s T \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) T"
    proof(cases rule: deadlocked_elims)
      case (lock x'')
      from `thr s t' = \<lfloor>(x', ln')\<rfloor>` `thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>` `0 < ln'\<^sub>f l`
      have False by auto
      thus ?thesis ..
    next
      case (wait x' ln')
      from wst' `waiting (wset s t')`
      have False by contradiction
      thus ?thesis ..
    next
      case (acquire x'' ln'' l'' t'')
      from `thr s t' = \<lfloor>(x'', ln'')\<rfloor>` `thr s t' = \<lfloor>(x', ln')\<rfloor>`
      have [simp]: "x' = x''" "ln' = ln''" by auto
      moreover from `deadlocked s t'' \<or> final_thread s t''`
      have "thr s t'' \<noteq> None"
	by(auto elim: deadlocked_thread_exists simp add: final_thread_def)
      with `0 < ln''\<^sub>f l''` `has_lock ((locks s)\<^sub>f l'') t''` `t' \<noteq> t''` `thr s t' = \<lfloor>(x'', ln'')\<rfloor>`
      show ?thesis by auto
    qed
  next
    fix t x w
    assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    show "wset s t \<noteq> \<lfloor>WokenUp w\<rfloor>"
    proof
      assume "wset s t = \<lfloor>WokenUp w\<rfloor>"
      moreover with tst have "not_final_thread s t"
        by(auto simp add: not_final_thread_iff)
      hence "deadlocked s t" by(rule deadlocked)
      ultimately show False using tst
        by(auto elim: deadlocked.cases simp add: waiting_def)
    qed
  qed
qed

lemma deadlock_eq_deadlocked':
  "deadlock = deadlocked'"
by(rule ext)(auto intro: deadlock_implies_deadlocked' deadlocked'_implies_deadlock)

lemma deadlock_no_red:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; deadlock s \<rbrakk> \<Longrightarrow> False"
unfolding deadlock_eq_deadlocked'
by(rule deadlocked'_no_red)

end

locale preserve_deadlocked = 
  final_thread_wf final r convert_RA + 
  multithreaded_start final r convert_RA start_state
  for final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and start_state :: "('l,'t,'x,'m,'w) state" +
  assumes can_lock_preserved: 
    "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; s -t'\<triangleright>ta'\<rightarrow> s';
       thr s t = \<lfloor>(x, ln)\<rfloor>; t \<turnstile> \<langle>x, shr s\<rangle> L \<wrong>; L \<noteq> {} \<rbrakk>
    \<Longrightarrow> t \<turnstile> \<langle>x, shr s'\<rangle> \<wrong>"
  and can_lock_devreserp:
    "\<lbrakk> RedT start_state tta s; s -t'\<triangleright>ta'\<rightarrow> s';
       thr s t = \<lfloor>(x, ln)\<rfloor>; t \<turnstile> \<langle>x, shr s'\<rangle> L \<wrong> \<rbrakk>
    \<Longrightarrow> \<exists>L'\<subseteq>L. t \<turnstile> \<langle>x, shr s\<rangle> L' \<wrong>"
begin

lemma redT_deadlocked_subset:
  assumes Red': "start_state -\<triangleright>ttas\<rightarrow>* s"
  and Red: "s -t\<triangleright>ta\<rightarrow> s'"
  and t'dead: "deadlocked s t'"
  shows "deadlocked s' t'"
proof -
  from Red have tndead: "\<not> deadlocked s t"
    by(auto dest: red_no_deadlock)
  with t'dead have t't: "t' \<noteq> t" by auto
  obtain las tas cas was obs where ta: "ta = (las, tas, cas, was, obs)" by (cases ta)
  obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by (cases s, auto)
  obtain ls' ts' m' ws' where s' [simp]: "s' = (ls', (ts', m'), ws')" by (cases s', auto)
  with s Red have "\<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>" by simp
  thus "deadlocked s' t'"
  proof(cases rule: redT_elims)
    case (normal x x' M)
    with ta s s' Red have red: "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', M\<rangle>"
      and est: "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and lot: "lock_ok_las ls t las"
      and cct: "thread_oks ts tas"
      and cdt: "cond_action_oks (ls, (ts, m), ws) t cas"
      and wst: "wset_actions_ok ws t was"
      and ls': "ls' = redT_updLs ls t las"
      and ts': "ts' = redT_updTs ts tas(t \<mapsto> (x', redT_updLns ls t no_wait_locks las))"
      and M: "M = m'"
      and ws': "redT_updWs t ws was ws'"
      by auto
    from red have "\<not> final x" by(auto dest: final_no_red)
    with tndead est s est wst have nafe: "\<not> all_final_except s (deadlocked s)"
      by(fastsimp simp add: all_final_except_def not_final_thread_iff)
    from t'dead show ?thesis
    proof(coinduct)
      case (deadlocked t'')
      note t''dead = this
      with Red have t''t: "t'' \<noteq> t"
	by(auto dest: red_no_deadlock)
      from t''dead show ?case
      proof(cases rule: deadlocked_elims)
	case (lock X)
	hence est'': "ts t'' = \<lfloor>(X, no_wait_locks)\<rfloor>"
	  and msE: "t'' \<turnstile> \<langle>X, m\<rangle> \<wrong>"
	  and csexdead: "\<forall>LT. t'' \<turnstile> \<langle>X, m\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and>
                                                        (\<exists>lt \<in> LT. must_wait s t'' lt t'))"
	  by auto
	from t''t Red est'' s s'
	have es't'': "ts' t'' = \<lfloor>(X, no_wait_locks)\<rfloor>"
	  by(auto elim!: redT_ts_Some_inv)
	note es't'' moreover
	from msE obtain X' M' ta where red': "t'' \<turnstile> \<langle>X, m\<rangle> -ta\<rightarrow> \<langle>X', M'\<rangle>"
	  by(auto elim: must_syncE)
	let ?LT = "collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
	from red' have csLT: "t'' \<turnstile> \<langle>X, m\<rangle> ?LT \<wrong>" by(auto intro: can_syncI)
	with csexdead[rule_format] have "?LT \<noteq> {}" by auto
	with est'' csLT have msE': "t'' \<turnstile> \<langle>X, m'\<rangle> \<wrong>"
	  by(rule can_lock_preserved[OF Red' Red, simplified])
	moreover
	{ fix LT
	  assume clL'': "t'' \<turnstile> \<langle>X, m'\<rangle> LT \<wrong>"
	  with clL'' est'' have "\<exists>LT'\<subseteq>LT. t'' \<turnstile> \<langle>X, m\<rangle> LT' \<wrong>"
	    by - (rule can_lock_devreserp[OF Red' Red, simplified shr_conv s], auto)
	  then obtain LT' where clL': "t'' \<turnstile> \<langle>X, m\<rangle> LT' \<wrong>"
	    and LL': "LT' \<subseteq> LT" by blast
	  with csexdead obtain t' lt
	    where t'dead: "deadlocked s t' \<or> final_thread s t'"
	    and lt: "lt \<in> LT" and mw: "must_wait s t'' lt t'"
	    by blast
	  from t'dead Red s have tt': "t \<noteq> t'"
	    by(auto dest: red_no_deadlock final_no_redT elim: final_threadE)
	  from mw have "must_wait s' t'' lt t'"
	  proof(cases rule: must_wait_elims)
	    case (lock l)
 	    from lot have "lock_actions_ok (ls\<^sub>f l) t (las\<^sub>f l)"
 	      by(simp add: lock_ok_las_def)
 	    with tt' `has_lock ((locks s)\<^sub>f l) t'` ls'
	    have hl't': "has_lock (ls'\<^sub>f l) t'" by(auto)
	    with `lt = Inl l` `t' \<noteq> t''` show ?thesis by auto
	  next
	    case thread
	    note nftt' = `not_final_thread s t'`
	    from tt' t'dead Red cct ts' ta have ts't': "ts' t' = ts t'"
	      by(auto elim!: deadlocked_thread_exists final_threadE intro: redT_updTs_Some)
	    from nftt' have "thr s t' \<noteq> None" by(auto)
	    with nftt' t'dead have "deadlocked s t'"
	      by(simp add: not_final_thread_final_thread_conv[symmetric])
	    hence "not_final_thread s' t'"
	    proof(cases rule: deadlocked_elims)
	      case (lock x'')
	      from `t' \<turnstile> \<langle>x'', shr s\<rangle> \<wrong>` have "\<not> final x''"
		by(auto elim: must_syncE)
	      with `thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>` ts't' show ?thesis
		by(auto intro: not_final_thread.intros)
	    next
	      case (wait x'' ln'')
	      from `\<not> final x` est `all_final_except s (deadlocked s)` wst
	      have "deadlocked s t" by(fastsimp dest: all_final_exceptD simp add: not_final_thread_iff)
	      with Red have False by(auto dest: red_no_deadlock)
	      thus ?thesis ..
	    next
	      case (acquire x'' ln'' l'' T'')
	      from `thr s t' = \<lfloor>(x'', ln'')\<rfloor>` `0 < ln''\<^sub>f l''` ts't'
	      show ?thesis by(auto intro: not_final_thread.intros)
	    qed
	    with `lt = Inr t'` show ?thesis by auto
	  qed
	  moreover
	  { assume "final_thread s t'"
	    from t'dead have "thr s t' \<noteq> None"
	      by(auto elim: deadlocked_elims final_threadE)
	    then obtain x' ln' where tst': "thr s t' = \<lfloor>(x', ln')\<rfloor>" by auto
	    with `final_thread s t'` have "final x'" 
	      and "wset s t' = None" and [simp]: "ln' = no_wait_locks"
	      by(auto elim: final_threadE)
	    with red have "x \<noteq> x'" by(auto dest: final_no_red)
	    with est tst' have "t \<noteq> t'" by auto
	    with Red cct ts' tst' ta have "thr s' t' = \<lfloor>(x', ln')\<rfloor>"
	      by(auto intro: redT_updTs_Some)
	    moreover from Red ws' `t \<noteq> t'` `wset s t' = None`
	    have "ws' t' = None" by(auto simp: redT_updWs_None_implies_None)
	    ultimately have "final_thread s' t'" using tst' `final x'`
	      by(auto simp add: final_thread_def) }
	  ultimately have "((deadlocked s t' \<or> deadlocked s' t') \<or> final_thread s' t') \<and> (\<exists>lt \<in> LT. must_wait s' t'' lt t')"
	    using t'dead `lt \<in> LT` by blast
	  hence "\<exists>t'. ((deadlocked s t' \<or> deadlocked s' t') \<or> final_thread s' t') \<and> (\<exists>lt \<in> LT. must_wait s' t'' lt t')"
	    by blast }
	moreover have "ws' t'' = None" using ws' t''t `wset s t'' = None` 
	  by(auto intro: redT_updWs_None_implies_None)
	ultimately show ?thesis by(auto)
      next
	case (wait x ln)
	from `all_final_except s (deadlocked s)` nafe have False by simp
	thus ?thesis by simp
      next
	case (acquire X ln l T)
	from t''t Red `thr s t'' = \<lfloor>(X, ln)\<rfloor>` s s'
	have es't'': "ts' t'' = \<lfloor>(X, ln)\<rfloor>"
	  by(auto elim!: redT_ts_Some_inv)
	moreover
	from `deadlocked s T \<or> final_thread s T`
	have "T \<noteq> t"
	proof(rule disjE)
	  assume "deadlocked s T"
	  with Red show ?thesis by(auto dest: red_no_deadlock)
	next
	  assume "final_thread s T"
	  with Red show ?thesis
	    by(auto dest!: final_no_redT simp add: final_thread_def)
	qed
	with Red `has_lock ((locks s)\<^sub>f l) T` have "has_lock ((locks s')\<^sub>f l) T"
	  by(simp add: redT_has_lock_inv)
	moreover
	from ws' `T \<noteq> t` have wset: "ws T = None \<Longrightarrow> ws' T = None"
	  by(auto intro: redT_updWs_None_implies_None)
	{ fix x
	  assume "thr s T = \<lfloor>(x, no_wait_locks)\<rfloor>"
	  with `T \<noteq> t` Red ts' cct est ta have "thr s' T = \<lfloor>(x, no_wait_locks)\<rfloor>"
	    by(auto intro: redT_updTs_Some) }
	moreover
	hence "final_thread s T \<Longrightarrow> final_thread s' T"
	  by(auto simp add: final_thread_def intro: wset)
        moreover from `\<not> waiting (wset s t'')` ws' t''t
        have "\<not> waiting (ws' t'')"
          by(auto simp add: redT_updWs_None_implies_None redT_updWs_WokenUp_imp_WokenUp not_waiting_iff)
	ultimately have ?deadlockedAcquire
	  using `0 < ln\<^sub>f l` `t'' \<noteq> T` `deadlocked s T \<or> final_thread s T` by(auto)
        thus ?thesis by simp
      qed
    qed
  next
    case (acquire x ln n)
    hence [simp]: "ta = (\<lambda>\<^isup>f [], [], [], [], convert_RA ln)" "ws' = ws" "m' = m"
      and ts': "ts' = ts(t \<mapsto> (x, no_wait_locks))"
      and ls': "ls' = acquire_all ls t ln"
      and tst: "ts t = \<lfloor>(x, ln)\<rfloor>" 
      and wst: "\<not> waiting (ws t)" by auto
    from t'dead show ?thesis
    proof(coinduct)
      case (deadlocked t'')
      note t''dead = this
      with Red have t''t: "t'' \<noteq> t"
	by(auto dest: red_no_deadlock)
      from t''dead show ?case
      proof(cases rule: deadlocked_elims)
	case (lock X)
	hence clnml: "\<And>LT. t'' \<turnstile> \<langle>X, shr s\<rangle> LT \<wrong>
                      \<Longrightarrow> \<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s t'' lt t')"
	  by blast
	note tst'' = `thr s t'' = \<lfloor>(X, no_wait_locks)\<rfloor>`
	with ts' t''t have ts't'': "thr s' t'' = \<lfloor>(X, no_wait_locks)\<rfloor>" by simp
	moreover 
	{ fix LT
	  assume "t'' \<turnstile> \<langle>X, shr s'\<rangle> LT \<wrong>"
	  hence "t'' \<turnstile> \<langle>X, shr s\<rangle> LT \<wrong>" by simp
	  then obtain T lt where Tdead: "deadlocked s T \<or> final_thread s T"
	    and "lt \<in> LT" and hlnft: "must_wait s t'' lt T"
	    by(blast dest: clnml)
	  from Tdead tst ts'
	  have "deadlocked s T \<or> final_thread s' T"
	    by(clarsimp simp add: final_thread_def)
	  hence "(deadlocked s T \<or> deadlocked s' T) \<or> final_thread s' T" by blast
	  moreover from hlnft have "must_wait s' t'' lt T"
	  proof(induct rule: must_wait_elims)
	    case (lock l')
	    from `has_lock ((locks s)\<^sub>f l') T` ls'
	    have "has_lock ((locks s')\<^sub>f l') T"
	      by(auto intro: has_lock_has_lock_acquire_locks)
	    with `T \<noteq> t''` `lt = Inl l'` show ?thesis by auto
	  next
	    case thread
	    from Tdead have "ts T \<noteq> None"
	      by(auto elim: deadlocked_elims final_threadE)
	    moreover from Tdead have "T \<noteq> t"
	    proof(rule disjE)
	      assume "deadlocked s T"
	      with Red show ?thesis by(auto dest: red_no_deadlock)
	    next
	      assume "final_thread s T"
	      with `0 < ln\<^sub>f n` tst show ?thesis
		by(auto simp add: final_thread_def)
	    qed
	    ultimately have "not_final_thread s' T" using `not_final_thread s T` ts'
	      by(auto simp add: not_final_thread_iff)
	    with `lt = Inr T` show ?thesis by auto
	  qed
	  ultimately have "\<exists>T. ((deadlocked s T \<or> deadlocked s' T) \<or> final_thread s' T) \<and> (\<exists>lt \<in> LT. must_wait s' t'' lt T)"
	    using `lt \<in> LT` by blast }
	moreover from `wset s t'' = None` have "wset s' t'' = None" by simp
	ultimately show ?thesis using `thr s t'' = \<lfloor>(X, no_wait_locks)\<rfloor>` `t'' \<turnstile> \<langle>X, shr s\<rangle> \<wrong>` by fastsimp
      next
	case (wait X LN)
	have "all_final_except (ls', (ts(t \<mapsto> (x, no_wait_locks)), m), ws) (deadlocked s)"
	proof(rule all_final_exceptI)
	  fix T
	  assume "not_final_thread (ls', (ts(t \<mapsto> (x, no_wait_locks)), m), ws) T"
	  hence "not_final_thread s T" using wst tst
	    by(auto simp add: not_final_thread_iff split: split_if_asm)
	  with `all_final_except s (deadlocked s)` `ts t = \<lfloor>(x, ln)\<rfloor>`
	  show "deadlocked s T" by -(erule all_final_exceptD)
	qed
	hence "all_final_except s' (deadlocked s)" by(simp add: ts')
	have "all_final_except s' (\<lambda>x. deadlocked s x \<or> deadlocked s' x)"
	  by(blast intro: all_final_except_mono[rule_format, OF _ `all_final_except s' (deadlocked s)`])
	with t''t `thr s t'' = \<lfloor>(X, LN)\<rfloor>` `waiting (wset s t'')` ts' 
        have ?deadlockedWait by simp
        thus ?thesis by simp
      next
	case (acquire X LN l T)
	from `thr s t'' = \<lfloor>(X, LN)\<rfloor>` t''t ts'
	have "thr s' t'' = \<lfloor>(X, LN)\<rfloor>" by(simp)
	moreover from `deadlocked s T \<or> final_thread s T` ts' tst 
	have "deadlocked s T \<or> final_thread s' T"
	  by(clarsimp simp add: final_thread_def)
	moreover from `has_lock ((locks s)\<^sub>f l) T` ls'
	have "has_lock ((locks s')\<^sub>f l) T"
	  by(auto intro: has_lock_has_lock_acquire_locks)
        moreover have "\<not> waiting (wset s' t'')" using `\<not> waiting (wset s t'')` by simp
	ultimately show ?thesis using `0 < LN\<^sub>f l` `t'' \<noteq> T` by blast
      qed
    qed
  qed
qed

end

end