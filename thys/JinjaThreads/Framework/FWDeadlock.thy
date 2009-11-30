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

lemma must_wait_elims [consumes 1, case_names lock thread]:
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

text{* Deadlock as a system-wide property *}

end

context multithreaded_base begin

definition
  deadlock :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where
  "deadlock s
   \<equiv> (\<exists>t. not_final_thread s t)
     \<and> (\<forall>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> \<not> final x \<and> wset s t = None
        \<longrightarrow> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t'))))
     \<and> (\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<exists>l. ln\<^sub>f l > 0) \<and> wset s t = None
        \<longrightarrow> (\<exists>l t'. ln\<^sub>f l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t'))"

end

context final_thread_wf begin

lemma deadlockI:
  "\<lbrakk> not_final_thread s t;
    \<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk>
    \<Longrightarrow> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t')));
    \<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ln\<^sub>f l > 0; wset s t = None \<rbrakk>
    \<Longrightarrow> \<exists>l t'. ln\<^sub>f l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t' \<rbrakk>
  \<Longrightarrow> deadlock s"
by(auto simp add: deadlock_def)

lemma deadlockE:
  assumes "deadlock s"
  obtains t ln x w
  where "thr s t = \<lfloor>(x, ln)\<rfloor>"
  and "not_final_thread s t"
  and "\<forall>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> \<not> final x \<and> wset s t = None
        \<longrightarrow> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t')))"
  and "\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<exists>l. ln\<^sub>f l > 0) \<and> wset s t = None \<longrightarrow> (\<exists>l t'. ln\<^sub>f l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t')"
using assms unfolding deadlock_def
by(blast)

lemma deadlockD1:
  assumes "deadlock s"
  and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
  and "\<not> final x"
  and "wset s t = None"
  obtains "\<langle>x, shr s\<rangle> \<wrong>"
  and "\<forall>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t'))"
using assms
unfolding deadlock_def by(blast)

lemma deadlockD2:
  assumes "deadlock s"
  and "thr s t = \<lfloor>(x, ln)\<rfloor>"
  and "ln\<^sub>f l > 0"
  and "wset s t = None"
  obtains l' t' where "ln\<^sub>f l' > 0" "t \<noteq> t'" "thr s t' \<noteq> None" "has_lock ((locks s)\<^sub>f l') t'"
using assms unfolding deadlock_def by blast

lemma all_waiting_implies_deadlock:
  assumes "not_final_thread s t"
  and "lock_thread_ok (locks s) (thr s)"
  and normal: "\<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk> 
               \<Longrightarrow> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t lt t')))"
  and acquire: "\<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None; ln\<^sub>f l > 0 \<rbrakk> \<Longrightarrow> \<exists>l'. ln\<^sub>f l' > 0 \<and> \<not> may_lock ((locks s)\<^sub>f l') t"
  shows "deadlock s"
proof(rule deadlockI)
  from `not_final_thread s t` show "not_final_thread s t" .
next
  fix T X
  assume tsT: "thr s T = \<lfloor>(X, no_wait_locks)\<rfloor>"
    and "\<not> final X" 
    and "wset s T = None"
  show "\<langle>X, shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>X, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. must_wait s T lt t')))"
    by(rule normal[OF tsT `\<not> final X` `wset s T = None`])
next
  fix T X LN l'
  assume "thr s T = \<lfloor>(X, LN)\<rfloor>"
    and "0 < LN\<^sub>f l'"
    and "wset s T = None"
  from acquire[OF `thr s T = \<lfloor>(X, LN)\<rfloor>` `wset s T = None`, OF `0 < LN\<^sub>f l'`]
  obtain l' where "0 < LN\<^sub>f l'" "\<not> may_lock ((locks s)\<^sub>f l') T" by blast
  then obtain t' where "T \<noteq> t'" "has_lock ((locks s)\<^sub>f l') t'"
    unfolding not_may_lock_conv by fastsimp
  moreover with `lock_thread_ok (locks s) (thr s)`
  have "thr s t' \<noteq> None" by(auto dest: lock_thread_okD)
  ultimately show "\<exists>l t'. 0 < LN\<^sub>f l \<and> T \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t'"
    using `0 < LN\<^sub>f l'` by(auto)
qed

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
    "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<langle>x, shr s\<rangle> \<wrong>; wset s t = None;
       \<And>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s t lt t') \<rbrakk>
     \<Longrightarrow> deadlocked s t"

| deadlockedWait:
    "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; all_final_except s (deadlocked s); wset s t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> deadlocked s t"

| deadlockedAcquire:
    "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ln\<^sub>f l > 0; has_lock ((locks s)\<^sub>f l) t'; t' \<noteq> t;
       deadlocked s t' \<or> final_thread s t' \<rbrakk> 
     \<Longrightarrow> deadlocked s t"


lemma deadlocked_elims [consumes 1, case_names lock wait acquire]:
  assumes "deadlocked s t"
  and lock: "\<And>x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<langle>x, shr s\<rangle> \<wrong>; wset s t = None;
                   \<And>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s t lt t') \<rbrakk>
             \<Longrightarrow> thesis"
  and wait: "\<And>x ln w. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; all_final_except s (deadlocked s); wset s t = \<lfloor>w\<rfloor>\<rbrakk> \<Longrightarrow> thesis"
  and acquire: "\<And>x ln l t'. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; 0 < ln\<^sub>f l; has_lock ((locks s)\<^sub>f l) t'; t \<noteq> t';
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
  proof(induct rule: redT_elims4)
    case (normal x x' ta')
    with ta have Pe: "\<langle>x, m\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>"
      and est: "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and lot: "lock_ok_las ls t las"
      and cct: "thread_oks ts tas"
      and cdt: "cond_action_oks (ls, (ts, m), ws) t cas"
      and wst: "ws t = None"
      and [simp]: "ta = observable_ta_of ta'"
      by(auto)
    show False
    proof(cases "all_final_except s (deadlocked s) \<and> (\<exists>w. ws t = \<lfloor>w\<rfloor>)")
      case True with wst show ?thesis by simp
    next
      case False
      with dead est s
      have mle: "\<langle>x, m\<rangle> \<wrong>"
	and cledead: "\<forall>LT. \<langle>x, m\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s t lt t'))"
	by - (erule deadlocked.cases, fastsimp+)+
      let ?LT = "collect_locks las <+> {t. Join t \<in> set cas}"
      from Pe ta have "\<langle>x, m\<rangle> ?LT \<wrong>" by(auto intro: can_syncI simp add: observable_ta_of_def)
      then obtain t' lt where "deadlocked s t' \<or> final_thread s t'"
	and lt: "lt \<in> ?LT" and mw: "must_wait s t lt t'"
	by(blast dest: cledead[rule_format])
      from mw show False
      proof(induct rule: must_wait_elims)
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
    show False
    proof(cases "all_final_except s (deadlocked s) \<and> (\<exists>w. ws t = \<lfloor>w\<rfloor>)")
      case True with `ws t = None` show ?thesis by simp
    next
      case False
      with dead `ts t = \<lfloor>(x, ln)\<rfloor>` `0 < ln\<^sub>f n` s
      obtain l t' where "0 < ln\<^sub>f l" "t \<noteq> t'"
	and "has_lock (ls\<^sub>f l) t'"
	by  -(erule deadlocked.cases, fastsimp+)
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
               \<Longrightarrow> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. must_wait s t lt t')))"
  and acquire: "\<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None; ln\<^sub>f l > 0 \<rbrakk> \<Longrightarrow> \<exists>l'. ln\<^sub>f l' > 0 \<and> \<not> may_lock ((locks s)\<^sub>f l') t"
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
      have "\<langle>x', m\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x', m\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s z lt t')))"
	by(auto dest: normal[simplified])
      then obtain "\<langle>x', m\<rangle> \<wrong>"
	and clnml: "\<And>LT. \<langle>x', m\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s z lt t')" by(blast)
      { fix LT
	assume "\<langle>x', m\<rangle> LT \<wrong>"
	then obtain t' where "thr s t' \<noteq> None" "\<exists>lt \<in> LT. must_wait s z lt t'"
	  by(blast dest: clnml)
	from `thr s t' \<noteq> None` obtain xln where "thr s t' = \<lfloor>xln\<rfloor>" by auto
	hence "not_final_thread s t' \<or> deadlocked s t' \<or> final_thread s t'"
	  by(rule not_final_thread_deadlocked_final_thread)
	with `\<exists>lt \<in> LT. must_wait s z lt t'`
	have "\<exists>t'. (not_final_thread s t' \<or> deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s z lt t')"
	  by blast }
      with `\<langle>x', m\<rangle> \<wrong>` `ts z = \<lfloor>(x', ln')\<rfloor>` `ws z = None` have ?case by(simp) }
    note c1 = this
    { assume "ws z = None"
      and "ln' \<noteq> no_wait_locks"
      from `ln' \<noteq> no_wait_locks` obtain l where "0 < ln'\<^sub>f l"
	by(auto simp add: neq_no_wait_locks_conv)
      with `ws z = None` `ts z = \<lfloor>(x', ln')\<rfloor>` 
      obtain l' where "0 < ln'\<^sub>f l'" "\<not> may_lock (ls\<^sub>f l') z"
	by(blast dest: acquire[simplified])
      then obtain t'' where "t'' \<noteq> z" "has_lock (ls\<^sub>f l') t''"
	unfolding not_may_lock_conv by blast
      with `lock_thread_ok (locks s) (thr s)`
      obtain x'' ln'' where "ts t'' = \<lfloor>(x'', ln'')\<rfloor>"
	by(auto elim!: lock_thread_ok_has_lockE)
      hence "(not_final_thread s t'' \<or> deadlocked s t'') \<or> final_thread s t''"
	by(clarsimp simp add: not_final_thread_iff final_thread_def)
      with `ws z = None` `0 < ln'\<^sub>f l'` `ts z = \<lfloor>(x', ln')\<rfloor>` `t'' \<noteq> z` `has_lock (ls\<^sub>f l') t''`
      have ?case by(simp)(blast) }
    note c2 = this
    { fix w
      assume "ws z = \<lfloor>w\<rfloor>"
      with `ts z = \<lfloor>(x', ln')\<rfloor>` s have ?case
	by -(rule disjI2, clarsimp simp add: all_final_except_def not_final_thread_iff) }
    note c3 = this
    from `not_final_thread s z` `thr s z = \<lfloor>(x', ln')\<rfloor>` show ?case
    proof(induct rule: not_final_thread_cases2)
      case final show ?thesis
      proof(cases "ws z")
	case None show ?thesis
	proof(cases "ln' = no_wait_locks")
	  case True with None final show ?thesis by(rule c1)
	next
	  case False with None show ?thesis by(rule c2)
	qed
      next
	case (Some w) thus ?thesis by(rule c3)
      qed
    next
      case wait_locks show ?thesis
      proof(cases "ws z")
	case None thus ?thesis using wait_locks by(rule c2)
      next
	case (Some w) thus ?thesis by(rule c3)
      qed
    next
      case (wait_set w)
      hence "ws z = \<lfloor>w\<rfloor>" by simp
      thus ?thesis by(rule c3)
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
      { fix w''
	assume "wset s t'' = \<lfloor>w''\<rfloor>"
	moreover
	with tst'' have nfine: "not_final_thread s t''"
	  by(blast intro: not_final_thread.intros)
	ultimately have ?case using tst''
	  by(blast intro: all_final_exceptI not_final_thread_final) }
      note c1 = this
      { assume wst'': "wset s t'' = None"
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
	ultimately obtain "\<langle>x'', shr s\<rangle> \<wrong>"
	  and clnml: "\<And>LT. \<langle>x'', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. must_wait s t'' lt t')"
	  using `thr s t'' = \<lfloor>(x'', ln'')\<rfloor>` `deadlock s`
	  by(blast elim: deadlockD1)
	{ fix LT
	  assume "\<langle>x'', shr s\<rangle> LT \<wrong>"
	  then obtain t' where "thr s t' \<noteq> None"
	    and mw: "\<exists>lt\<in>LT. must_wait s t'' lt t'" by(blast dest: clnml)
	  from `thr s t' \<noteq> None` have "not_final_thread s t' \<or> final_thread s t'"
	    by(auto simp add: final_thread_def not_final_thread_iff)
	  with mw have "\<exists>t'.(not_final_thread s t' \<or> deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt\<in>LT. must_wait s t'' lt t')"
	    by fastsimp }
	with `\<langle>x'', shr s\<rangle> \<wrong>` tst'' `wset s t'' = None` have ?case by(simp) }
      note c3 = this
      from `not_final_thread s t''` tst'' show ?case
      proof(induct rule: not_final_thread_cases2)
	case final show ?thesis
	proof(cases "wset s t''")
	  case None show ?thesis
	  proof(cases "ln'' = no_wait_locks")
	    case True with None show ?thesis by(rule c3)
	  next
	    case False with None show ?thesis by(rule c2)
	  qed
	next
	  case (Some w) thus ?thesis by(rule c1)
	qed
      next
	case wait_locks show ?thesis
	proof(cases "wset s t''")
	  case None thus ?thesis using wait_locks by(rule c2)
	next
	  case (Some w) thus ?thesis by(rule c1)
	qed
      next
	case (wait_set w) thus ?thesis by(rule c1)
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
    thus "\<langle>x', shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x', shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t''. thr s t'' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t' lt t'')))"
    proof(cases rule: deadlocked_elims)
      case (lock x'')
      hence lock: "\<And>LT. \<langle>x'', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>T. (deadlocked s T \<or> final_thread s T) \<and> (\<exists>lt \<in> LT. must_wait s t' lt T)"
	by blast
      from `thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>` `thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>`
      have [simp]: "x' = x''" by auto
      have "\<And>LT. \<langle>x'', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t''. thr s t'' \<noteq> None \<and> (\<exists>lt \<in> LT. must_wait s t' lt t'')"
	by -(drule lock, auto elim!: deadlocked_thread_exists final_threadE)
      with `\<langle>x'', shr s\<rangle> \<wrong>` show ?thesis by(auto)
    next
      case (wait x'' ln'' w'')
      from `wset s t' = None` `wset s t' = \<lfloor>w''\<rfloor>`
      have False by simp
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
      and "wset s t' = None"
    hence "not_final_thread s t'" by(auto intro: not_final_thread_wait_locks)
    hence "deadlocked s t'" by(rule deadlocked)
    thus "\<exists>l T. 0 < ln'\<^sub>f l \<and> t' \<noteq> T \<and> thr s T \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) T"
    proof(cases rule: deadlocked_elims)
      case (lock x'')
      from `thr s t' = \<lfloor>(x', ln')\<rfloor>` `thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>` `0 < ln'\<^sub>f l`
      have False by auto
      thus ?thesis ..
    next
      case (wait x' ln' w')
      from `wset s t' = None` `wset s t' = \<lfloor>w'\<rfloor>`
      have False by simp
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

end