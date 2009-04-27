(*  Title:      JinjaThreads/Compiler/Correctness1Threaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of Stage 1: multithreaded case} *}

theory Correctness1Threaded imports Correctness1 J0Threaded begin


lemma red1_new_thread_heap: "\<lbrakk>P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t ex h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h = hp s'"
  and reds1_new_thread_heap: "\<lbrakk>P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t ex h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h = hp s'"
apply(induct rule: red1_reds1.inducts)
apply(fastsimp elim: red_ext_new_thread_heap)+
done

abbreviation mred1 :: "J1_prog \<Rightarrow> (addr,addr,(expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list,heap,addr) semantics"
where "mred1 P \<equiv> \<lambda>((ex, exs), h) ta ((ex', exs'), h'). P \<turnstile>1 \<langle>ex/exs, h\<rangle> -ta\<rightarrow> \<langle>ex'/exs', h'\<rangle>"

lemma Red1_mthr: "multithreaded (mred1 P)"
apply(unfold_locales)
apply(fastsimp elim!: Red1.cases dest: red1_new_thread_heap)
done

abbreviation final_expr1 :: "(expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list \<Rightarrow> bool" where
  "final_expr1 \<equiv> \<lambda>(ex, exs). final (fst ex) \<and> exs = []"

interpretation Red1_mthr: multithreaded final_expr1 "mred1 P"
by(rule Red1_mthr)

lemma Red1_mthr': "multithreaded (mred1' P)"
apply(unfold_locales)
apply(fastsimp elim!: Red1.cases dest: red1_new_thread_heap)
done

interpretation Red1_mthr': multithreaded final_expr1 "mred1' P"
by(rule Red1_mthr')

lemma red0_mthr': "multithreaded (mred0' P)"
apply(unfold_locales)
apply(fastsimp elim!: red0.cases dest: red_new_thread_heap)
done

interpretation red0_mthr': multithreaded final_expr0 "mred0' P"
by(rule red0_mthr')

lemma red0_Red1_FWbase': "FWbisimulation_base (mred0' P) (mred1' (compP1 P))"
by(unfold_locales)

interpretation red0_Red1_FWbase':
  FWbisimulation_base final_expr0 "mred0' P" final_expr1 "mred1' (compP1 P)" "bisim_red0_Red1"
by(rule red0_Red1_FWbase')

lemma red0_Red1_FWbase:
  "FWbisimulation_base (mred0 P) (mred1 (compP1 P))"
by(unfold_locales)

interpretation red0_Red1_FWbase:
  FWbisimulation_base final_expr0 "mred0 P" final_expr1 "mred1 (compP1 P)" bisim_red0_Red1
by(rule red0_Red1_FWbase)

lemma red0_Red1_FWbisim':
  assumes wf: "wf_J_prog P"
  shows "FWbisimulation final_expr0 (mred0' P) final_expr1 (mred1' (compP1 P)) bisim_red0_Red1"
proof -
  interpret bisimulation "mred0' P" "mred1' (compP1 P)" bisim_red0_Red1 "ta_bisim bisim_red0_Red1"
    using wf by(rule bisimulation_red0_Red1)
  show ?thesis
  proof
    fix x1 m1 x2 m2
    assume "bisim_red0_Red1 (x1, m1) (x2, m2)"
    thus "final_expr0 x1 = final_expr1 x2"
      by(auto simp add: bisim_red0_Red1_def final_iff elim: bisim_list.cases)
  next
    fix x m1 x' m2 x1 x2 ta1 x1' m1' ta2 x2' m2'
    assume b: "bisim_red0_Red1 (x, m1) (x', m2)"
      and bo: "bisim_red0_Red1 (x1, m1) (x2, m2)"
      and red1: "mred0' P (x1, m1) ta1 (x1', m1')"
      and red2: "mred1' (compP1 P) (x2, m2) ta2 (x2', m2')"
      and bo': "bisim_red0_Red1 (x1', m1') (x2', m2')"
      and tb: "ta_bisim bisim_red0_Red1 ta1 ta2"
    from b have "m1 = m2" by(auto simp add: bisim_red0_Red1_def split_beta)
    moreover from bo' have "m1' = m2'" by(auto simp add: bisim_red0_Red1_def split_beta)
    moreover from red1 have "hext m1 m1'" by(auto simp add: split_beta dest: red_hext_incr elim!: red0.cases)
    ultimately show "bisim_red0_Red1 (x, m1') (x', m2')" using b
      by(auto simp add: bisim_red0_Red1_def split_beta)
  qed
qed

definition lock_oks :: "(addr,thread_id) locks \<Rightarrow> (addr,thread_id,(('a,'b) exp \<times> 'c) \<times> (('a,'b) exp \<times> 'c) list) thread_info \<Rightarrow> bool" where
  "lock_oks ls ts \<equiv> \<forall>t. (case (ts t) of None    \<Rightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t = 0)
                            | \<lfloor>((ex, exs), ln)\<rfloor> \<Rightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_lockss (map fst (ex # exs)) l))"

lemma red_UnlockFail_UnlockFail: "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l) \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l = [UnlockFail]"
  and reds_UnlockFail_UnlockFail: "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l) \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l = [UnlockFail]"
apply(induct rule: red_reds.inducts)
apply(fastsimp split: split_if_asm simp add: finfun_upd_apply dest: red_external_UnlockFail_UnlockFail)+
done


lemma red0_mthr_eq_red0_mthr':
  assumes lok: "lock_oks (locks s) (thr s)"
  shows "red0_mthr.redT P s = red0_mthr'.redT P s"
proof(intro ext)
  fix tta s'
  show "red0_mthr.redT P s tta s' = red0_mthr'.redT P s tta s'" (is "?lhs = ?rhs")
  proof
    assume "?lhs" thus ?rhs
    proof cases
      case (redT_normal x S ta x' m' t S')
      hence [simp]: "S = s" "S' = s'" "tta = (t, ta)" by simp_all
      note thrS = `thr S t = \<lfloor>(x, no_wait_locks)\<rfloor>`
      note aoe = `red0_mthr.actions_ok S t ta` 
      obtain ex exs where x [simp]: "x = (ex, exs)" by(cases x)
      obtain ex' exs' where x' [simp]: "x' = (ex', exs')" by(cases x')
      from `mred0 P (x, shr S) ta (x', m')`
      have red: "P \<turnstile>0 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>" by simp
      moreover {
	fix a
	assume "UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f a)"
	with red have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f a = [UnlockFail]"
	  by(auto elim!: red0.cases dest: red_UnlockFail_UnlockFail)
	moreover from aoe have "lock_actions_ok ((locks s)\<^sub>f a) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f a)"	
	  by(auto simp add: lock_ok_las_def)
	ultimately have "has_locks ((locks s)\<^sub>f a) t = 0" by simp
	with lok thrS have "expr_lockss (map fst (ex # exs)) a = 0"
	  apply(cases ex)
	  apply(auto simp add: lock_oks_def)
	  apply fastsimp+
	  done }
      ultimately have "mred0' P (x, shr s) ta (x', m')" by simp
      hence "red0_mthr'.redT P s (t, ta) s'"
	using thrS `wset S t = None` aoe `S' = final_thread.redT_upd S t ta x' m'`
	unfolding `S = s` `S' = s'` by(rule red0_mthr'.redT.redT_normal)
      thus ?thesis unfolding `tta = (t, ta)` .
    next
      case (redT_acquire S t x ln n S')
      from `thr S t = \<lfloor>(x, ln)\<rfloor>` `wset S t = None` `may_acquire_all (locks S) t ln`
	`0 < ln\<^sub>f n` `S' = (acquire_all (locks S) t ln, (thr S(t \<mapsto> (x, no_wait_locks)), shr S), wset S)`
      show ?thesis unfolding `tta = (t, \<epsilon>)` `s' = S'` `s = S`
	by(rule red0_mthr'.redT_acquire)
    qed
  next
    assume ?rhs thus ?lhs
    proof(cases)
      case (redT_normal x S ta x' m' t S')
      from `mred0' P (x, shr S) ta (x', m')` have "mred0 P (x, shr S) ta (x', m')"
	by(auto simp add: split_beta)
      thus ?thesis using `thr S t = \<lfloor>(x, no_wait_locks)\<rfloor>` `wset S t = None`
       `red0_mthr.actions_ok S t ta` `S' = final_thread.redT_upd S t ta x' m'`
	unfolding `s = S` `tta = (t, ta)` `s' = S'` by(rule red0_mthr.redT.redT_normal)
    next
      case (redT_acquire S t x ln n S')
      from `thr S t = \<lfloor>(x, ln)\<rfloor>` `wset S t = None` `may_acquire_all (locks S) t ln`
	`0 < ln\<^sub>f n` `S' = (acquire_all (locks S) t ln, (thr S(t \<mapsto> (x, no_wait_locks)), shr S), wset S)`
      show ?thesis unfolding `tta = (t, \<epsilon>)` `s' = S'` `s = S`
	by(rule red0_mthr.redT_acquire)
    qed
  qed
qed
   
lemma red1_UnlockFail_UnlockFail: "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l) \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l = [UnlockFail]"
  and reds1_UnlockFail_UnlockFail: "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l) \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l = [UnlockFail]"
by(induct rule: red1_reds1.inducts)(fastsimp split: split_if_asm simp add: finfun_upd_apply dest: red_external_UnlockFail_UnlockFail)+

lemma Red1_mthr_eq_Red1_mthr':
  assumes lok: "lock_oks (locks s) (thr s)"
  shows "Red1_mthr.redT P s = Red1_mthr'.redT P s"
proof(intro ext)
  fix tta s'
  show "Red1_mthr.redT P s tta s' = Red1_mthr'.redT P s tta s'" (is "?lhs = ?rhs")
  proof
    assume "?lhs" thus ?rhs
    proof cases
      case (redT_normal x S ta x' m' t S')
      hence [simp]: "S = s" "S' = s'" "tta = (t, ta)" by simp_all
      note thrS = `thr S t = \<lfloor>(x, no_wait_locks)\<rfloor>`
      note aoe = `Red1_mthr.actions_ok S t ta` 
      obtain ex exs where x [simp]: "x = (ex, exs)" by(cases x)
      obtain ex' exs' where x' [simp]: "x' = (ex', exs')" by(cases x')
      from `mred1 P (x, shr S) ta (x', m')`
      have red: "P \<turnstile>1 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>" by simp
      moreover {
	fix a
	assume "UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f a)"
	with red have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f a = [UnlockFail]"
	  by(auto elim!: Red1.cases dest: red1_UnlockFail_UnlockFail)
	moreover from aoe have "lock_actions_ok ((locks s)\<^sub>f a) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f a)"	
	  by(auto simp add: lock_ok_las_def)
	ultimately have "has_locks ((locks s)\<^sub>f a) t = 0" by simp
	with lok thrS have "expr_lockss (map fst (ex # exs)) a = 0"
	  apply(cases ex)
	  apply(auto simp add: lock_oks_def)
	  apply fastsimp+
	  done }
      ultimately have "mred1' P (x, shr s) ta (x', m')" by simp
      hence "Red1_mthr'.redT P s (t, ta) s'"
	using thrS `wset S t = None` aoe `S' = final_thread.redT_upd S t ta x' m'`
	unfolding `S = s` `S' = s'` by(rule Red1_mthr'.redT.redT_normal)
      thus ?thesis unfolding `tta = (t, ta)` .
    next
      case (redT_acquire S t x ln n S')
      from `thr S t = \<lfloor>(x, ln)\<rfloor>` `wset S t = None` `may_acquire_all (locks S) t ln`
	`0 < ln\<^sub>f n` `S' = (acquire_all (locks S) t ln, (thr S(t \<mapsto> (x, no_wait_locks)), shr S), wset S)`
      show ?thesis unfolding `tta = (t, \<epsilon>)` `s' = S'` `s = S`
	by(rule Red1_mthr'.redT_acquire)
    qed
  next
    assume ?rhs thus ?lhs
    proof(cases)
      case (redT_normal x S ta x' m' t S')
      from `mred1' P (x, shr S) ta (x', m')` have "mred1 P (x, shr S) ta (x', m')"
	by(auto simp add: split_beta)
      thus ?thesis using `thr S t = \<lfloor>(x, no_wait_locks)\<rfloor>` `wset S t = None`
       `Red1_mthr.actions_ok S t ta` `S' = final_thread.redT_upd S t ta x' m'`
	unfolding `s = S` `tta = (t, ta)` `s' = S'`
	by(rule Red1_mthr.redT.redT_normal)
    next
      case (redT_acquire S t x ln n S')
      from `thr S t = \<lfloor>(x, ln)\<rfloor>` `wset S t = None` `may_acquire_all (locks S) t ln`
	`0 < ln\<^sub>f n` `S' = (acquire_all (locks S) t ln, (thr S(t \<mapsto> (x, no_wait_locks)), shr S), wset S)`
      show ?thesis unfolding `tta = (t, \<epsilon>)` `s' = S'` `s = S`
	by(rule Red1_mthr.redT_acquire)
    qed
  qed
qed


lemma bisim_sync_ok:
  "bisim Vs e e' xs \<Longrightarrow> sync_ok e"
  "bisim Vs e e' xs \<Longrightarrow> sync_ok e'"

  and bisims_sync_oks:
  "bisims Vs es es' xs \<Longrightarrow> sync_oks es"
  "bisims Vs es es' xs \<Longrightarrow> sync_oks es'"
apply(induct rule: bisim_bisims.inducts)
apply(auto intro: not_contains_insync_sync_ok not_contains_insyncs_sync_oks)
done  

lemma expr_locks_inline_call:
  "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> expr_locks (inline_call e' e) = (\<lambda>l. expr_locks e' l + expr_locks e l)"
  and expr_lockss_inline_calls:
  "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> expr_lockss (inline_calls e' es) = (\<lambda>l. expr_locks e' l + expr_lockss es l)"
apply(induct e and es)
apply(auto simp add: add_ac is_vals_conv split: split_if_asm split del: split_if)
apply(auto intro: ext)
done

definition sync_es_oks ::  "(addr,thread_id,(('a,'b) exp \<times> 'c) \<times> (('a,'b) exp \<times> 'c) list) thread_info \<Rightarrow> 'm \<Rightarrow> bool"
  where "sync_es_oks \<equiv> ts_ok (\<lambda>(ex, exs) h. \<forall>e \<in> fst ` set (ex # exs). sync_ok e)"

lemma assumes wf: "wf_J_prog P"
  shows expr_locks_new_thread0:
  "\<lbrakk> extTA2J0 P,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t (ex, exs) h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> expr_lockss (map fst (ex # exs)) = (\<lambda>ad. 0)"

  and expr_locks_new_thread0':
  "\<lbrakk> extTA2J0 P,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t (ex, exs) h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> expr_lockss (map fst (ex # exs)) = (\<lambda>ad. 0)"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  then obtain C fs where subThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" and ext: "extNTA2J0 P (C, run, t) = (ex, exs)"
    by(fastsimp elim!: red_external.cases split: heapobj.split_asm dest: Array_widen)
  from sub_Thread_sees_run[OF wf subThread] obtain D pns body
    where sees: "P \<turnstile> C sees run: []\<rightarrow>Void = (pns, body) in D" by auto
  from sees_wf_mdecl[OF wf this] obtain T where "P,[this \<mapsto> Class D] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
  with sees ext show ?case by(auto simp add: extNTA2J_def)
qed(auto)


lemma red0_preserves_lock_oks:
  assumes wf: "wf_J_prog P"
  and Red: "red0_mthr.redT P s1 ta1 s1'"
  and loks: "lock_oks (locks s1) (thr s1)"
  and sync: "sync_es_oks (thr s1) (shr s1)"
  shows "lock_oks (locks s1') (thr s1')"
using Red
proof(cases rule: red0_mthr.redT.cases)
  case (redT_normal x s ta x' m' t s')
  hence [simp]: "s1 = s" "ta1 = (t, ta)" "s1' = s'" by simp_all
  obtain ex exs where x: "x = (ex, exs)" by (cases x)
  obtain ex' exs' where x': "x' = (ex', exs')" by (cases x')
  note thrst = `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>`
  note wst = `wset s t = None`
  note s' = `s' = final_thread.redT_upd s t ta x' m'`
  note aoe = `red0_mthr.actions_ok s t ta`
  from `(\<lambda>((ex, exs), h) ta ((ex', exs'), h'). P \<turnstile>0 \<langle>ex/exs,h\<rangle> -ta\<rightarrow> \<langle>ex'/exs',h'\<rangle>) (x, shr s) ta (x', m')` x x'
  have red: "P \<turnstile>0 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>" by simp
  thus ?thesis
  proof cases
    case (red0Red e h x TA e' h' x' EXS)
    hence [simp]: "ex = (e, x)" "EXS = exs" "shr s = h" "ta = TA" "ex' = (e', x')" "exs' = exs" "m' = h'" by auto
    { fix t'
      assume None: "(redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (((e', x'), exs'), redT_updLns (locks s) t (snd (the (thr s t))) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))) t' = None"
      { fix l
	from aoe have "lock_actions_ok ((locks s)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)" by(auto simp add: lock_ok_las_def)
	with None have "has_locks ((redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t' = has_locks ((locks s)\<^sub>f l) t'"
	  by(auto split: split_if_asm)
	also from loks None have "has_locks ((locks s)\<^sub>f l) t' = 0" unfolding lock_oks_def
	  by(force split: split_if_asm dest!: redT_updTs_None)
	finally have "has_locks ((redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t' = 0" . }
      hence "\<forall>l. has_locks ((redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t' = 0" .. }
    moreover {
      fix t' eX eXS LN
      assume Some: "(redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (((e', x'), exs'), redT_updLns (locks s) t (snd (the (thr s t))) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))) t' = \<lfloor>((eX, eXS), LN)\<rfloor>"
      { fix l
	from aoe have lao: "lock_actions_ok ((locks s)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)" by(auto simp add: lock_ok_las_def)
	have "has_locks ((redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t' + LN\<^sub>f l = expr_lockss (map fst (eX # eXS)) l"
	proof(cases "t = t'")
	  case True
	  from loks thrst x
	  have "has_locks ((locks s)\<^sub>f l) t = expr_locks e l + expr_lockss (map fst exs) l"
	    by(force simp add: lock_oks_def)
	  hence "lock_expr_locks_ok ((locks s)\<^sub>f l) t 0 (int (expr_locks e l + expr_lockss (map fst exs) l))"
	    by(simp add: lock_expr_locks_ok_def)
	  with lao have "lock_expr_locks_ok (upd_locks ((locks s)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)) t (upd_threadRs 0 ((locks s)\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l))
 (upd_expr_lock_actions (int (expr_locks e l + expr_lockss (map fst exs) l)) (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l))"
	    by(rule upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok)
	  moreover from sync thrst x have "sync_ok e" unfolding sync_es_oks_def by(auto dest: ts_okD)
	  from red_update_expr_locks[OF wf `extTA2J0 P,P \<turnstile> \<langle>e,(h, x)\<rangle> -TA\<rightarrow> \<langle>e',(h', x')\<rangle>` this]
	  have "upd_expr_locks (int \<circ> expr_locks e) \<lbrace>TA\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'" by simp
	  hence "upd_expr_lock_actions (int (expr_locks e l)) (\<lbrace>TA\<rbrace>\<^bsub>l\<^esub>\<^sub>f l) = int (expr_locks e' l)"
	    by(simp add: upd_expr_locks_def expand_fun_eq)
	  ultimately show ?thesis using lao Some thrst x True s' by(auto simp add: lock_expr_locks_ok_def upd_expr_locks_def)
	next
	  case False
	  from aoe have tok: "thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by auto
	  show ?thesis
	  proof(cases "thr s t' = None")
	    case True
	    with Some tok False obtain m where nt: "NewThread t' (eX, eXS) m \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>"
	      and [simp]: "LN = no_wait_locks"
	      by(auto dest: redT_updTs_new_thread)
	    note expr_locks_new_thread0[OF wf `extTA2J0 P,P \<turnstile> \<langle>e,(h, x)\<rangle> -TA\<rightarrow> \<langle>e',(h', x')\<rangle>` nt]
	    moreover from loks True have "has_locks ((locks s)\<^sub>f l) t' = 0"
	      by(force simp add: lock_oks_def)
	    ultimately show ?thesis using lao False by simp
	  next	    
	    case False
	    with Some `t \<noteq> t'` tok 
	    have "thr s t' = \<lfloor>((eX, eXS), LN)\<rfloor>" by(fastsimp dest: redT_updTs_Some[OF _ tok])
	    with loks tok lao `t \<noteq> t'` show ?thesis
	      by(cases eX)(auto simp add: lock_oks_def)
	  qed
	qed }
      hence "\<forall>l. has_locks ((redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t' + LN\<^sub>f l = expr_lockss (map fst (eX # eXS)) l" .. }
    ultimately show ?thesis unfolding lock_oks_def s' `s1' = s'` x'
      by(auto split: option.split simp del: fun_upd_apply)
  next
    case (red0Call e a M vs h C fs Ts T pns body D x EXS)
    from wf `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
    obtain T' where "P,[pns [\<mapsto>] Ts, this \<mapsto> Class D] \<turnstile> body :: T'"
      by(auto simp add: wf_mdecl_def dest!: sees_wf_mdecl)
    with `length vs = length pns` `length Ts = length pns`
    have "expr_locks (blocks (pns, Ts, vs, body)) = (\<lambda>l. 0)"
      by(simp add: expr_locks_blocks)(erule WT_expr_locks)
    thus ?thesis using red0Call thrst loks
      unfolding lock_oks_def s' `s1' = s'` x' x
      by auto force+
  next
    case (red0Return e aMvs e' x' x EXS h)
    thus ?thesis using thrst loks
      unfolding lock_oks_def s' `s1' = s'` x' x
      apply auto
       apply(erule allE)
       apply(erule conjE)
       apply(erule disjE)
        prefer 2
        apply blast
       apply force
      apply(force simp add: expr_locks_inline_call add_ac)
      done
  qed
next
  case (redT_acquire s t x ln n s')
  thus ?thesis using loks unfolding lock_oks_def
    apply auto
     apply force
    apply(case_tac "ln\<^sub>f l::nat")
     apply simp
     apply(erule allE)
     apply(erule conjE)
     apply(erule allE)+
     apply(erule (1) impE)
     apply(erule_tac x=l in allE)
     apply fastsimp
    apply(erule may_acquire_allE)
    apply(erule allE)
    apply(erule_tac x=l in allE)
    apply(erule impE)
     apply simp
    apply(simp only: has_locks_acquire_locks_conv)
    apply(erule conjE)
    apply(erule allE)+
    apply(erule (1) impE)
    apply(erule_tac x=l in allE)
    apply simp
    done
qed

lemma bisim_list_sync_oks:
  assumes "bisim_list exs exs'"
  shows "e \<in> fst ` set exs \<Longrightarrow> sync_ok e"
        "e' \<in> fst ` set exs' \<Longrightarrow> sync_ok e'"
using assms
apply(induct rule: bisim_list.induct)
apply(auto intro: bisim_sync_ok)
done

lemma bisim_red0_Red1_sync_es_oks:
  assumes "bisim_red0_Red1 ((ex, exs), h) ((ex', exs'), h')"
  shows "e \<in> fst ` set (ex # exs) \<Longrightarrow> sync_ok e"
  and "e' \<in> fst ` set (ex' # exs') \<Longrightarrow> sync_ok e'"
using assms
by(auto intro: bisim_list_sync_oks bisim_sync_ok simp add: bisim_red0_Red1_def)

lemma mbisim_bisim_red0_Red1_sync_es_oks:
  assumes bisim: "red0_Red1_FWbase.mbisim s1 s2"
  shows "sync_es_oks (thr s1) m"  "sync_es_oks (thr s2) m'"
unfolding sync_es_oks_def
proof -
  from bisim have l: "locks s1 = locks s2" and w: "wset s1 = wset s2"
  and t: "\<And>t. case thr s1 t of None \<Rightarrow> thr s2 t = None
                        | \<lfloor>(x1, ln)\<rfloor> \<Rightarrow> \<exists>x2. thr s2 t = \<lfloor>(x2, ln)\<rfloor> \<and> bisim_red0_Red1 (x1, shr s1) (x2, shr s2)"
    unfolding red0_Red1_FWbase.mbisim_def red0_Red1_FWbase.tbisim_def by auto
  show "ts_ok (\<lambda>(ex, exs) h. \<forall>e\<in>fst ` set (ex # exs). sync_ok e) (thr s1) m"
  proof(rule ts_okI)
    fix t x1 ln
    assume t1: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>"
    with t[of t] obtain x2 where t2: "thr s2 t = \<lfloor>(x2, ln)\<rfloor>"
      and bisim': "bisim_red0_Red1 (x1, shr s1) (x2, shr s2)" by auto
    from bisim' show "(\<lambda>(ex, exs) h. \<forall>e\<in>fst ` set (ex # exs). sync_ok e) x1 m"
      by(cases x2)(force intro: bisim_red0_Red1_sync_es_oks)
  qed
  show "ts_ok (\<lambda>(ex, exs) h. \<forall>e\<in>fst ` set (ex # exs). sync_ok e) (thr s2) m'"
  proof(rule ts_okI)
    fix t x2 ln
    assume t2: "thr s2 t = \<lfloor>(x2, ln)\<rfloor>"
    with t[of t] obtain x1 where t1: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>"
      and bisim': "bisim_red0_Red1 (x1, shr s1) (x2, shr s2)" by fastsimp
    from bisim' show "(\<lambda>(ex, exs) h. \<forall>e\<in>fst ` set (ex # exs). sync_ok e) x2 m'"
      by(cases x1)(force intro: bisim_red0_Red1_sync_es_oks)
  qed
qed

lemma red0_Red1_lock_oks_eq:
  assumes bisim: "red0_Red1_FWbase.mbisim s1 s2"
  shows "lock_oks (locks s1) (thr s1) = lock_oks (locks s2) (thr s2)"
proof -
  from bisim have l: "locks s1 = locks s2" and w: "wset s1 = wset s2"
    and t: "\<And>t. case thr s1 t of None \<Rightarrow> thr s2 t = None
                          | \<lfloor>(x1, ln)\<rfloor> \<Rightarrow> \<exists>x2. thr s2 t = \<lfloor>(x2, ln)\<rfloor> \<and> bisim_red0_Red1 (x1, shr s1) (x2, shr s2)"
    unfolding red0_Red1_FWbase.mbisim_def red0_Red1_FWbase.tbisim_def by auto
  show ?thesis
  proof
    assume "lock_oks (locks s1) (thr s1)"
    thus "lock_oks (locks s2) (thr s2)" using l t
      unfolding lock_oks_def apply auto
       apply(erule_tac x=t in meta_allE)
       apply(force)
      apply(erule_tac x=t in meta_allE)
      apply(auto simp add: bisim_red0_Red1_def expand_fun_eq dest!: bisim_list_expr_lockss_eq)
      apply(force)
      done
  next
    assume "lock_oks (locks s2) (thr s2)"
    thus "lock_oks (locks s1) (thr s1)" using l t
      unfolding lock_oks_def apply auto
       apply(erule_tac x=t in meta_allE)
       apply(force)
      apply(erule_tac x=t in meta_allE)
      apply(auto simp add: bisim_red0_Red1_def expand_fun_eq dest!: bisim_list_expr_lockss_eq)
      done
  qed
qed

abbreviation mbisim_red0_Red1 :: "((addr,addr,(expr \<times> locals) \<times> (expr \<times> locals) list,heap,addr) state,
                                 (addr,addr,(expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list,heap,addr) state) bisim" where
 "mbisim_red0_Red1 \<equiv> (\<lambda>s1 s2. red0_Red1_FWbase.mbisim s1 s2 \<and> lock_oks (locks s1) (thr s1) \<and> lock_oks (locks s2) (thr s2))"

lemma red0_Red1_FWbisim:
  assumes wf: "wf_J_prog P"
  shows "bisimulation (red0_mthr.redT P) (Red1_mthr.redT (compP1 P))
                      mbisim_red0_Red1 red0_Red1_FWbase.mta_bisim"
proof
  fix s1 s2 ta1 s1'
  assume "mbisim_red0_Red1 s1 s2"
    and red1: "red0_mthr.redT P s1 ta1 s1'"
  hence bisim: "red0_Red1_FWbase.mbisim s1 s2"
    and lok1: "lock_oks (locks s1) (thr s1)"
    and lok2: "lock_oks (locks s2) (thr s2)" by simp_all
  from bisimulation.simulation1[OF FWbisimulation.mbisim_bisimulation[OF red0_Red1_FWbisim'[OF wf]], OF bisim] red1
  obtain s2' ta2 where "Red1_mthr.redT (compP1 P) s2 ta2 s2'"
    and bisim': "red0_Red1_FWbase.mbisim s1' s2'"  and "red0_Red1_FWbase.mta_bisim ta1 ta2"
    unfolding red0_mthr_eq_red0_mthr'[OF lok1] Red1_mthr_eq_Red1_mthr'[OF lok2] by(blast)
  moreover from red1 lok1 mbisim_bisim_red0_Red1_sync_es_oks[OF bisim]
  have "lock_oks (locks s1') (thr s1')" by-(rule red0_preserves_lock_oks[OF wf])
  moreover with bisim' have "lock_oks (locks s2') (thr s2')" by(simp add: red0_Red1_lock_oks_eq)
  ultimately show "\<exists>s2' ta2. Red1_mthr.redT (compP1 P) s2 ta2 s2' \<and> mbisim_red0_Red1 s1' s2' \<and>
                          red0_Red1_FWbase.mta_bisim ta1 ta2" by blast
next
  fix s1 s2 ta2 s2'
  assume "mbisim_red0_Red1 s1 s2"
    and red2: "Red1_mthr.redT (compP1 P) s2 ta2 s2'"
  hence bisim: "red0_Red1_FWbase.mbisim s1 s2"
    and lok1: "lock_oks (locks s1) (thr s1)"
    and lok2: "lock_oks (locks s2) (thr s2)" by(simp_all)
  from bisimulation.simulation2[OF FWbisimulation.mbisim_bisimulation[OF red0_Red1_FWbisim'[OF wf]], OF bisim] red2
  obtain s1' ta1 where red1: "red0_mthr.redT P s1 ta1 s1'"
    and bisim': "red0_Red1_FWbase'.mbisim s1' s2'" and "red0_Red1_FWbase.mta_bisim ta1 ta2"
    unfolding red0_mthr_eq_red0_mthr'[OF lok1] Red1_mthr_eq_Red1_mthr'[OF lok2] by blast
  moreover from red1 lok1 mbisim_bisim_red0_Red1_sync_es_oks[OF bisim]
  have "lock_oks (locks s1') (thr s1')" by-(rule red0_preserves_lock_oks[OF wf])
  moreover with bisim' have "lock_oks (locks s2') (thr s2')" by(simp add: red0_Red1_lock_oks_eq)
  ultimately show "\<exists>s1' ta1. red0_mthr.redT P s1 ta1 s1' \<and> mbisim_red0_Red1 s1' s2' \<and>
                          red0_Red1_FWbase.mta_bisim ta1 ta2" by blast
qed

end