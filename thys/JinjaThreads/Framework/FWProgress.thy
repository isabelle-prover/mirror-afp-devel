(*  Title:      JinjaThreads/Framework/FWProgress.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Progress theorem for the multithreaded semantics} *}

theory FWProgress imports FWDeadlock FWWellformSem begin


locale preserve_deadlocked = final_thread_wf + preserve_lock_behav begin

lemma redT_deadlocked_subset:
  assumes Red': "start_state -\<triangleright>ttas\<rightarrow>* s"
  and Red: "s -t\<triangleright>ta\<rightarrow> s'"
  and t'dead: "deadlocked s t'"
  shows "deadlocked s' t'"
proof -
  from Red have tndead: "\<not> deadlocked s t"
    by(auto dest: red_no_deadlock)
  with t'dead have t't: "t' \<noteq> t" by auto
  obtain las tas cas was where ta: "ta = (las, tas, cas, was)" by (cases ta, auto)
  obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by (cases s, auto)
  obtain ls' ts' m' ws' where s' [simp]: "s' = (ls', (ts', m'), ws')" by (cases s', auto)
  with s Red have "\<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>" by simp
  thus "deadlocked s' t'"
  proof(induct rule: redT_elims4)
    case (normal x x')
    with ta s s' Red have red: "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
      and est: "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and lot: "lock_ok_las ls t las"
      and cct: "thread_oks ts m' tas"
      and cdt: "cond_action_oks (ls, (ts, m), ws) t cas"
      and wst: "ws t = None"
      and ws': "ws' = redT_updWs ws t was"
      and es': "ts' = redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))"
      and ls': "ls' = redT_updLs ls t las"
      by auto
    from red have "\<not> final x" by(auto dest: final_no_red)
    with tndead est s have nafe: "\<not> all_final_except ts (deadlocked s)"
      by(fastsimp simp add: all_final_except_def)
    from t'dead show ?thesis
    proof(coinduct)
      case (deadlocked t'')
      note t''dead = this
      with Red have t''t: "t'' \<noteq> t"
	by(auto dest: red_no_deadlock)
      from t''dead show ?case
      proof(induct rule: deadlocked_elims)
	case (lock X)
	hence est'': "ts t'' = \<lfloor>(X, no_wait_locks)\<rfloor>"
	  and msE: "\<langle>X, m\<rangle> \<wrong>"
	  and csexdead: "\<forall>LT. \<langle>X, m\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and>
                                                  (\<exists>lt \<in> LT. must_wait s t'' lt t'))"
	  by auto
	from t''t Red est'' s s'
	have es't'': "ts' t'' = \<lfloor>(X, no_wait_locks)\<rfloor>"
	  by(auto elim!: redT_ts_Some_inv)
	note es't'' moreover
	from msE obtain X' M' ta
	  where red': "\<langle>X, m\<rangle> -ta\<rightarrow> \<langle>X', M'\<rangle>"
	  by(auto elim: must_syncE)
	from est'' msE have msE': "\<langle>X, m'\<rangle> \<wrong>"
	  by(rule must_lock_preserved[OF Red' Red, simplified])
	moreover
	{ fix LT
	  assume clL'': "\<langle>X, m'\<rangle> LT \<wrong>"
	  with msE' have "LT \<noteq> {}"
	    by(auto elim!: can_syncE dest!: must_syncD simp add: collect_locks_def Plus_eq_empty_conv)
	  with clL'' est'' have "\<exists>LT'\<subseteq>LT. \<langle>X, m\<rangle> LT' \<wrong>"
	    by - (rule can_lock_devreserp[OF Red' Red, simplified shr_conv s], auto)
	  then obtain LT' where clL': "\<langle>X, m\<rangle> LT' \<wrong>"
	    and LL': "LT' \<subseteq> LT" by blast
	  with csexdead obtain t' lt
	    where t'dead: "deadlocked s t' \<or> final_thread s t'"
	    and lt: "lt \<in> LT" and mw: "must_wait s t'' lt t'"
	    by blast
	  from t'dead Red s have tt': "t \<noteq> t'"
	    by(auto dest: red_no_deadlock final_no_redT elim: final_threadE)
	  from mw have "must_wait s' t'' lt t'"
	  proof(induct rule: must_wait_elims)
	    case (lock l)
 	    from lot have "lock_actions_ok (ls l) t (las l)"
 	      by(simp add: lock_ok_las_def)
 	    with tt' ls' `has_lock (locks s l) t'`
	    have hl't': "has_lock (ls' l) t'" by(auto)
	    with `lt = Inl l` `t' \<noteq> t''` show ?thesis by auto
	  next
	    case thread
	    note nftt' = `not_final_thread s t'`
	    from tt' t'dead Red cct es' ta have ts't': "ts' t' = ts t'"
	      by(auto elim!: deadlocked_thread_exists final_threadE intro: redT_updTs_Some)
	    from nftt' have "thr s t' \<noteq> None" by(auto)
	    with nftt' t'dead have "deadlocked s t'"
	      by(simp add: not_final_thread_final_thread_conv[symmetric])
	    hence "not_final_thread s' t'"
	    proof(induct rule: deadlocked_elims)
	      case (lock x'')
	      from `\<langle>x'', shr s\<rangle> \<wrong>` have "\<not> final x''"
		by(auto elim: must_syncE)
	      with `thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>` ts't' show ?thesis
		by(auto intro: not_final_thread.intros)
	    next
	      case (wait x'' ln'' w'')
	      from `\<not> final x` est `all_final_except (thr s) (deadlocked s)`
	      have "deadlocked s t" by(auto dest: all_final_exceptD)
	      with Red have False by(auto dest: red_no_deadlock)
	      thus ?thesis ..
	    next
	      case (acquire x'' ln'' l'' T'')
	      from `thr s t' = \<lfloor>(x'', ln'')\<rfloor>` `0 < ln'' l''` ts't'
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
	    with Red cct es' tst' ta have "thr s' t' = \<lfloor>(x', ln')\<rfloor>"
	      by(auto intro: redT_updTs_Some)
	    moreover from Red ws' `t \<noteq> t'` `wset s t' = None`
	    have "ws' t' = None" by(auto simp: redT_updWs_None_implies_None)
	    ultimately have "final_thread s' t'" using tst' `final x'`
	      by(auto simp add: final_thread_def) }
	  ultimately have "((deadlocked s t' \<or> deadlocked s' t') \<or> final_thread s' t') \<and> (\<exists>lt \<in> LT. must_wait s' t'' lt t')"
	    using t'dead `lt \<in> LT` by blast
	  hence "\<exists>t'. ((deadlocked s t' \<or> deadlocked s' t') \<or> final_thread s' t') \<and> (\<exists>lt \<in> LT. must_wait s' t'' lt t')"
	    by blast }
	ultimately show ?case by(auto)
      next
	case (wait x ln w)
	from `all_final_except (thr s) (deadlocked s)` nafe have False by simp
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
	with Red `has_lock (locks s l) T` have "has_lock (locks s' l) T"
	  by(simp add: redT_has_lock_inv)
	moreover
	from ws' `T \<noteq> t` have wset: "ws T = None \<Longrightarrow> ws' T = None"
	  by(auto intro: redT_updWs_None_implies_None)
	{ fix x
	  assume "thr s T = \<lfloor>(x, no_wait_locks)\<rfloor>"
	  with `T \<noteq> t` Red es' cct est ta have "thr s' T = \<lfloor>(x, no_wait_locks)\<rfloor>"
	    by(auto intro: redT_updTs_Some) }
	moreover
	hence "final_thread s T \<Longrightarrow> final_thread s' T"
	  by(auto simp add: final_thread_def intro: wset)
	ultimately show ?thesis
	  using `0 < ln l` `t'' \<noteq> T` `deadlocked s T \<or> final_thread s T`
	  apply -
	  apply(rule disjI2)
	  apply(rule disjI2)
	  apply(auto)
	  done
      qed
    qed
  next
    case (acquire x ln n)
    note [simp] = `ta = \<epsilon>` `ws' = ws` `m' = m`
    note ts' = `ts' = ts(t \<mapsto> (x, no_wait_locks))`
    note ls' = `ls' = acquire_all ls t ln`
    note tst = `ts t = \<lfloor>(x, ln)\<rfloor>`
    from t'dead show ?thesis
    proof(coinduct)
      case (deadlocked t'')
      note t''dead = this
      with Red have t''t: "t'' \<noteq> t"
	by(auto dest: red_no_deadlock)
      from t''dead show ?case
      proof(induct rule: deadlocked_elims)
	case (lock X)
	hence clnml: "\<And>LT. \<langle>X, shr s\<rangle> LT \<wrong>
                      \<Longrightarrow> \<exists>t'. (deadlocked s t' \<or> final_thread s t') \<and> (\<exists>lt \<in> LT. must_wait s t'' lt t')"
	  by blast
	note tst'' = `thr s t'' = \<lfloor>(X, no_wait_locks)\<rfloor>`
	with ts' t''t have ts't'': "thr s' t'' = \<lfloor>(X, no_wait_locks)\<rfloor>" by simp
	moreover 
	{ fix LT
	  assume "\<langle>X, shr s'\<rangle> LT \<wrong>"
	  hence "\<langle>X, shr s\<rangle> LT \<wrong>" by simp
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
	    from `has_lock (locks s l') T` ls'
	    have "has_lock (locks s' l') T"
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
	      with `0 < ln n` tst show ?thesis
		by(auto simp add: final_thread_def)
	    qed
	    ultimately have "not_final_thread s' T" using `not_final_thread s T` ts'
	      by(auto simp add: not_final_thread_iff)
	    with `lt = Inr T` show ?thesis by auto
	  qed
	  ultimately have "\<exists>T. ((deadlocked s T \<or> deadlocked s' T) \<or> final_thread s' T) \<and> (\<exists>lt \<in> LT. must_wait s' t'' lt T)"
	    using `lt \<in> LT` by blast }
	ultimately show ?case using `thr s t'' = \<lfloor>(X, no_wait_locks)\<rfloor>` `\<langle>X, shr s\<rangle> \<wrong>`
	  by fastsimp
      next
	case (wait X LN w)
	have "all_final_except (ts(t \<mapsto> (x, no_wait_locks))) (deadlocked s)"
	proof(rule all_final_exceptI)
	  fix T X' LN'
	  assume ts'T: "(ts(t \<mapsto> (x, no_wait_locks))) T = \<lfloor>(X', LN')\<rfloor>"
	    and ndeadT: "\<not> deadlocked s T"
	  with `all_final_except (thr s) (deadlocked s)` `ts t = \<lfloor>(x, ln)\<rfloor>` ts'T ndeadT
	  show "final X'"
	    by(cases "T = t", auto elim!: all_final_exceptD)
	qed
	hence "all_final_except (thr s') (deadlocked s)" by(simp add: ts')
	have "all_final_except (thr s') (\<lambda>x. deadlocked s x \<or> deadlocked s' x)"
	  by(blast intro: all_final_except_mono[rule_format, OF _ `all_final_except (thr s') (deadlocked s)`])
	with t''t `thr s t'' = \<lfloor>(X, LN)\<rfloor>` `wset s t'' = \<lfloor>w\<rfloor>` ts' show ?case
	  by-(rule disjI2, rule disjI1, simp)
      next
	case (acquire X LN l T)
	from `thr s t'' = \<lfloor>(X, LN)\<rfloor>` t''t ts'
	have "thr s' t'' = \<lfloor>(X, LN)\<rfloor>" by(simp)
	moreover from `deadlocked s T \<or> final_thread s T` ts' tst 
	have "deadlocked s T \<or> final_thread s' T"
	  by(clarsimp simp add: final_thread_def)
	moreover from `has_lock (locks s l) T` ls'
	have "has_lock (locks s' l) T"
	  by(auto intro: has_lock_has_lock_acquire_locks)
	ultimately show ?thesis using `0 < LN l` `t'' \<noteq> T` by blast
      qed
    qed
  qed
qed

lemma RedT_deadlocked_subset:
  "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; deadlocked start_state t' \<rbrakk> \<Longrightarrow> deadlocked s t'"
apply(induct rule: RedT_induct')
 apply(assumption)
by(insert must_lock_preserved can_lock_devreserp)(rule redT_deadlocked_subset)

end


locale progress = final_thread_wf + wf_progress + wf_red + preserves_lock_thread_ok +
  fixes deadlock :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool"
  assumes waiting_deadlock:
    "\<lbrakk> multithreaded.RedT final r start_state ttas s; final_thread_wf.not_final_thread final s t;
       \<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk> 
       \<Longrightarrow> multithreaded.must_sync r x (shr s) \<and>
          (\<forall>LT. multithreaded.can_sync r x (shr s) LT \<longrightarrow> (\<exists>t'. \<exists>lt \<in> LT. final_thread_wf.must_wait final s t lt t'));
       \<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None; ln l > 0 \<rbrakk> \<Longrightarrow> \<exists>l'. ln l' > 0 \<and> \<not> may_lock (locks s l') t \<rbrakk>
     \<Longrightarrow> deadlock s"
begin

lemma redT_progress:
  assumes Red: "start_state -\<triangleright>ttas\<rightarrow>* s"
  assumes nfine: "not_final_thread s t"
  and ndead: "\<not> deadlock s"
  shows "\<exists>t' ta' s'. s -t'\<triangleright>ta'\<rightarrow> s'"
proof -
thm waiting_deadlock
  from ndead
  have "\<exists>t x ln l. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> wset s t = None \<and>
         (ln = no_wait_locks \<and> \<not> final x \<and> 
          (\<langle>x, shr s\<rangle> \<wrong> \<longrightarrow> (\<exists>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt \<in> LT. \<not> must_wait s t lt t'))) \<or>
          ln l > 0 \<and> (\<forall>l. ln l > 0 \<longrightarrow> may_lock (locks s l) t))"
    apply -
    apply(erule contrapos_np)
    apply(rule waiting_deadlock[OF Red nfine])
    by(blast)+
  then obtain t x ln l
    where "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "wset s t = None"
    and a: "(ln = no_wait_locks \<and> \<not> final x \<and> 
            (\<langle>x, shr s\<rangle> \<wrong> \<longrightarrow> (\<exists>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt \<in> LT. \<not> must_wait s t lt t'))) \<or>
             ln l > 0 \<and> (\<forall>l. ln l > 0 \<longrightarrow> may_lock (locks s l) t))"
    by blast

  obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by (cases s, auto)
  note conform = wf_red[OF Red, simplified]
  from `thr s t = \<lfloor>(x, ln)\<rfloor>` have tst: "ts t = \<lfloor>(x, ln)\<rfloor>" by simp
  from s a have a: "(ln = no_wait_locks \<and> \<not> final x \<and> 
            (\<langle>x, m\<rangle> \<wrong> \<longrightarrow> (\<exists>LT. \<langle>x, m\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt \<in> LT. \<not> must_wait s t lt t'))) \<or>
             ln l > 0 \<and> (\<forall>l. ln l > 0 \<longrightarrow> may_lock (ls l) t))" by simp
  thus ?thesis
  proof(rule disjE)
    assume "ln = no_wait_locks \<and> \<not> final x \<and> (\<langle>x, m\<rangle> \<wrong> \<longrightarrow> (\<exists>LT. \<langle>x, m\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt\<in>LT. \<not> must_wait s t lt t')))"
    then obtain [simp]: "ln = no_wait_locks" and nfine': "\<not> final x"
      and mlclml: "\<langle>x, m\<rangle> \<wrong> \<Longrightarrow> \<exists>LT. \<langle>x, m\<rangle> LT \<wrong> \<and> (\<forall>t'. \<forall>lt\<in>LT. \<not> must_wait s t lt t')"
      by blast
    from `thr s t = \<lfloor>(x, ln)\<rfloor>` nfine'
    obtain x'' m'' ta' where red: "\<langle>x, m\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
      by(auto intro: wf_progressE[OF Red])
    { assume ml: "\<langle>x, m\<rangle> \<wrong>"
      then obtain LT
	where cl': "\<langle>x, m\<rangle> LT \<wrong>"
	and mw: "\<And>t' lt. lt \<in> LT \<Longrightarrow> \<not> must_wait s t lt t'"
	by(blast dest: mlclml)
      from cl'
      have "\<exists>ta''' x''' m'''. \<langle>x, m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle> \<and> LT = collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>}"
	by (fastsimp elim!: can_syncE)
      then obtain ta''' x''' m'''
	where red'': "\<langle>x, m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle>"
	and L: "LT = collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>}"
	by blast
      from tst[simplified] red''
      obtain ta'' x'' m''
	where red': "\<langle>x, m\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
	and cct: "thread_oks ts m'' \<lbrace>ta''\<rbrace>\<^bsub>t\<^esub>"
	and lot: "lock_ok_las' ls t \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
	and collect: "collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub>"
	and cao: "cond_action_oks' (ls, (ts, m), ws) t \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>"
	and join: "collect_cond_actions \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>"
	by -(rule wf_redE[OF Red], auto)
      { fix l
	assume "Inl l \<in> LT"
	hence "\<forall>t'. \<not> must_wait s t (Inl l) t'" by-(rule allI mw)+
	hence "\<forall>t'. t \<noteq> t' \<longrightarrow> \<not> has_lock (ls l) t'" by(fastsimp)
	hence "may_lock (ls l) t"
	  by-(rule classical, auto simp add: not_may_lock_conv) }
      note mayl = this
      from mw L have mayj: "\<And>t. Inr t \<in> LT \<Longrightarrow> \<not> not_final_thread s t" by(auto)
      from collect L mayl
      have "\<forall>l\<in>collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>. may_lock (ls l) t" by auto
      with lot have "\<And>l. l \<in> collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<Longrightarrow> may_lock (ls l) t"
	by - (rule lock_ok_las'_collect_locks'_may_lock)
      with lot have "lock_ok_las ls t \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
	by -(rule lock_ok_las'_collect_locks_lock_ok_las)
      moreover from mayj join L
      have "cond_action_oks (ls, (ts, m), ws) t \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub>"
	by(fastsimp intro: may_join_cond_action_oks)
      moreover note red' cct tst `wset s t = None`
      ultimately have ?thesis by(fastsimp intro: redT_normal) }
    moreover
    { assume ml: "\<not> \<langle>x, m\<rangle> \<wrong>"
      with red have "\<exists>ta x'' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x'', m'\<rangle> \<and> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> (\<forall>t. Join t \<notin> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
	by(cases ta', fastsimp simp add: collect_locks_def must_sync_def)
      then obtain ta''' x''' m'''
	where red'': "\<langle>x, m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle>"
	and collect'': "collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> = {}"
	and join'': "\<And>t. Join t \<notin> set \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>" by blast
      from tst[simplified] red''
      obtain ta'' x'' m''
	where red': "\<langle>x, m\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
	and cct: "thread_oks ts m'' \<lbrace>ta''\<rbrace>\<^bsub>t\<^esub>"
	and lot: "lock_ok_las' ls t \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
	and collect: "collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub>"
	and cao: "cond_action_oks' (ls, (ts, m), ws) t \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>"
	and join: "collect_cond_actions \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta'''\<rbrace>\<^bsub>c\<^esub>"
	by(auto intro: wf_redE[OF Red, simplified])
      from collect collect'' lot
      have "\<And>l. l \<in> collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<Longrightarrow> may_lock (ls l) t"
	by-(erule lock_ok_las'_collect_locks'_may_lock, auto)
      with lot have "lock_ok_las ls t \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
	by -(rule lock_ok_las'_collect_locks_lock_ok_las)
      moreover from join join'' have "cond_action_oks s t \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub>"
	by(auto intro: may_join_cond_action_oks)
      moreover note red' cct tst `wset s t = None`
      ultimately have ?thesis by(fastsimp intro: redT_normal) }
    ultimately show ?thesis by blast
  next
    assume "0 < ln l \<and> (\<forall>l. 0 < ln l \<longrightarrow> may_lock (ls l) t)"
    hence "0 < ln l" "\<And>l. 0 < ln l \<Longrightarrow> may_lock (ls l) t" by(auto)
    hence "may_acquire_all ls t ln" by(auto intro: may_acquire_allI)
    with tst `wset s t = None` `0 < ln l`
    show ?thesis by(fastsimp intro: redT_acquire)
  qed
qed

end

lemma (in final_thread_wf) lock_thread_ok_must_wait_thread_exists:
  "\<lbrakk> lock_thread_ok (locks s) (thr s); must_wait s t lt t' \<rbrakk> \<Longrightarrow> thr s t' \<noteq> None"
by(auto dest: lock_thread_okD elim!: must_wait_elims)
  

lemma (in final_thread_wf) progress_deadlock:
  assumes wf_progress: "wf_progress final r start_state"
  and wf_red: "wf_red final r start_state"
  and lto: "preserves_lock_thread_ok final r start_state"
  shows "progress final r start_state deadlock"
proof(rule progress.intro[OF final_r.final_thread_wf_axioms wf_progress wf_red lto progress_axioms.intro])
  fix ttas s t
  assume Red: "start_state -\<triangleright>ttas\<rightarrow>* s"
    and tst: "not_final_thread s t"
    and normal: "\<And>t x. \<lbrakk>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None\<rbrakk>
              \<Longrightarrow> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. \<exists>lt\<in>LT. must_wait s t lt t'))"
    and acquire: "\<And>t x ln l. \<lbrakk>thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None; 0 < ln l\<rbrakk> \<Longrightarrow> \<exists>l'. 0 < ln l' \<and> \<not> may_lock (locks s l') t"
  from lto Red have lok: "lock_thread_ok (locks s) (thr s)"
    by(rule preserves_lock_thread_ok.lock_thread_ok)
  with tst normal acquire show "deadlock s"
    by-(rule all_waiting_implies_deadlock,(blast dest: lock_thread_ok_must_wait_thread_exists[OF lok])+)
qed




lemma (in final_thread_wf) progress_deadlocked':
  assumes wf_progress: "wf_progress final r start_state"
  and wf_red: "wf_red final r start_state"
  and lto: "preserves_lock_thread_ok final r start_state"
  shows "progress final r start_state deadlocked'"
proof(rule progress.intro[OF final_r.final_thread_wf_axioms wf_progress wf_red lto progress_axioms.intro])
  fix ttas s t x ln
  assume Red: "start_state -\<triangleright>ttas\<rightarrow>* s"
    and tst: "not_final_thread s t"
    and normal: "\<And>t x. \<lbrakk>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None\<rbrakk>
              \<Longrightarrow> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>t'. \<exists>lt\<in>LT. must_wait s t lt t'))"
    and acquire: "\<And>t x ln l. \<lbrakk>thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None; 0 < ln l\<rbrakk> \<Longrightarrow> \<exists>l'. 0 < ln l' \<and> \<not> may_lock (locks s l') t"
  from lto Red have lok: "lock_thread_ok (locks s) (thr s)"
    by(rule preserves_lock_thread_ok.lock_thread_ok)
  show "deadlocked' s"
  proof(rule deadlocked'I)
    from tst show "not_final_thread s t" .
  next
    fix t'
    assume "not_final_thread s t'"
    with normal acquire `lock_thread_ok (locks s) (thr s)`
    show "deadlocked s t'" by -(rule all_waiting_deadlocked,(blast dest: lock_thread_ok_must_wait_thread_exists[OF lok])+)
  qed
qed


end
