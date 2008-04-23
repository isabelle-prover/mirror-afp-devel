(*  Title:      JinjaThreads/Framework/FWSemantics.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{The multithreaded semantics} *}

theory FWSemantics imports FWWellform FWLockingThread FWWait FWCondAction begin

locale multithreaded = final_thread +
  constrains final :: "'x \<Rightarrow> bool"
  fixes r :: "('l,'t,'x,'m,'w) semantics" ("_ -_\<rightarrow> _" [50,0,50] 80)
begin

abbreviation
  r_syntax :: "'x \<Rightarrow> 'm \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool" ("\<langle>_, _\<rangle> -_\<rightarrow> \<langle>_, _\<rangle>" [0,0,0,0,0] 80)
where
  "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<equiv> (x, m) -ta\<rightarrow> (x', m')"

inductive
  redT :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<times> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool" and
  redT_syntax1 :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool" ("_ -_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)
where
  "s -t\<triangleright>ta\<rightarrow> s' \<equiv> redT s (t, ta) s'"
|  redT_normal:
  "\<lbrakk> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>;
     thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; wset s t = None;
     lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks (thr s) m' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>;
     s' = (redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>,
           ((redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)), m'),
           redT_updWs (wset s) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>) \<rbrakk>
  \<Longrightarrow> s -t\<triangleright>ta\<rightarrow> s'"

| redT_acquire:
  "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None;
     may_acquire_all (locks s) t ln; ln n > 0;
     s' = (acquire_all (locks s) t ln, (thr s(t \<mapsto> (x, no_wait_locks)), shr s), wset s) \<rbrakk>
  \<Longrightarrow> s -t\<triangleright>\<epsilon>\<rightarrow> s'"

abbreviation
  redT_syntax2 :: "('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets
                   \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w) thread_action
                   \<Rightarrow> ('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool"
                  ("\<langle>_, _, _\<rangle> -_\<triangleright>_\<rightarrow> \<langle>_, _, _\<rangle>" [0,0,0,0,0,0,0,0] 80)
where
  "\<langle>ls, tsm, ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', tsm', ws'\<rangle> \<equiv> (ls, tsm, ws) -t\<triangleright>ta\<rightarrow> (ls', tsm', ws')"

lemma redT_elims [consumes 1, case_names normal acquire]:
  assumes red: "s -t\<triangleright>ta\<rightarrow> s'"
  and normal: "\<And>x x'. \<lbrakk> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', shr s'\<rangle>; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
                        lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks (thr s) (shr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; wset s t = None;
                        cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>;
                        locks s' = redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>;
                        thr s' = (redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>));
                        wset s' = redT_updWs (wset s) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> thesis"
  and acquire: "\<And>x ln n. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ta = \<epsilon>; wset s t = None; may_acquire_all (locks s) t ln; ln n > 0;
                           locks s' = acquire_all (locks s) t ln;
                           thr s' = thr s(t \<mapsto> (x, no_wait_locks));
                           wset s' = wset s; shr s' = shr s \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
using red
apply -
apply(erule redT.cases)
 apply(rule normal, fastsimp+)
apply(rule acquire, fastsimp+)
done

lemma redT_elims4 [consumes 1, case_names normal acquire]:
  assumes red: "\<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>"
  and normal: "\<And>x x'. \<lbrakk> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; ts t = \<lfloor>(x, no_wait_locks)\<rfloor>;
                        lock_ok_las ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks ts m' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; ws t = None; cond_action_oks (ls, (ts, m), ws) t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>;
                        ls' = redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>;
                        ts' = (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (x', redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>));
                        ws' = redT_updWs ws t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> thesis"
  and acquire: "\<And>x ln n. \<lbrakk> ts t = \<lfloor>(x, ln)\<rfloor>; ta = \<epsilon>; ws t = None; may_acquire_all ls t ln; ln n > 0;
                           ls' = acquire_all ls t ln;
                           ts' = ts(t \<mapsto> (x, no_wait_locks));
                           ws' = ws; m' = m \<rbrakk> \<Longrightarrow> thesis"
  shows "thesis"
using red
apply -
apply(erule redT.cases)
 apply(rule normal, fastsimp+)
apply(rule acquire, fastsimp+)
done

definition
  RedT :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> ('l,'t,'x,'m,'w) thread_action) list \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
          ("_ -\<triangleright>_\<rightarrow>* _" [50,0,50] 80)
where
  "RedT \<equiv> stepify_pred redT"

abbreviation
  RedT_syntax :: "('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets
                  \<Rightarrow> ('t \<times> ('l,'t,'x,'m,'w) thread_action) list 
                  \<Rightarrow> ('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool"
                 ("\<langle>_, _, _\<rangle> -\<triangleright>_\<rightarrow>* \<langle>_, _, _\<rangle>" [0,0,0,0,0,0,0] 80)
where
  "\<langle>ls, tsm, ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', tsm', ws'\<rangle> \<equiv> (ls, tsm, ws) -\<triangleright>ttas\<rightarrow>* (ls', tsm', ws')"

lemma RedTI:
  "stepify_pred redT s ttas s' \<Longrightarrow> RedT s ttas s'"
by(simp add: RedT_def)

lemma RedTE:
  "\<lbrakk> RedT s ttas s'; stepify_pred redT s ttas s' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: RedT_def)

lemma RedTD:
  "RedT s ttas s' \<Longrightarrow> stepify_pred redT s ttas s'"
by(simp add: RedT_def)

lemma RedT_induct [consumes 1, case_names refl step]:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s';
     \<And>s. P s [] s;
     \<And>s ttas s' t ta s''. \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; P s ttas s'; s' -t\<triangleright>ta\<rightarrow> s'' \<rbrakk> \<Longrightarrow> P s (ttas @ [(t, ta)]) s''\<rbrakk>
  \<Longrightarrow> P s ttas s'"
by(auto intro: stepify_pred.induct simp add: RedT_def)

lemma RedT_induct4 [consumes 1, case_names refl step]:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>;
     \<And>ls ts m ws. P ls ts m ws [] ls ts m ws;
     \<And>ls ts m ws ttas ls' ts' m' ws' t ta ls'' ts'' m'' ws''.
       \<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; 
         P ls ts m ws ttas ls' ts' m' ws';
         \<langle>ls', (ts', m'), ws'\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls'', (ts'', m''), ws''\<rangle> \<rbrakk> 
       \<Longrightarrow> P ls ts m ws (ttas @ [(t, ta)]) ls'' ts'' m'' ws'' \<rbrakk>
  \<Longrightarrow> P ls ts m ws ttas ls' ts' m' ws'"
unfolding RedT_def
by(erule stepify_pred_induct4', auto)

lemma RedT_induct' [consumes 1, case_names refl step]:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s';
     P s [] s;
     \<And>ttas s' t ta s''. \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; P s ttas s'; s' -t\<triangleright>ta\<rightarrow> s'' \<rbrakk> \<Longrightarrow> P s (ttas @ [(t, ta)]) s''\<rbrakk>
  \<Longrightarrow> P s ttas s'"
  unfolding RedT_def
apply(erule stepify_pred_induct', blast)
apply(case_tac b, blast)
done

lemma RedT_lift_preserveD:
  assumes Red: "s -\<triangleright>ttas\<rightarrow>* s'"
  and P: "P s"
  and preserve: "\<And>s t tas s'. \<lbrakk> s -t\<triangleright>tas\<rightarrow> s'; P s \<rbrakk> \<Longrightarrow> P s'"
  shows "P s'"
  using Red P
  by(induct rule: RedT_induct)(auto intro: preserve)

lemma RedT_lift_preserveD4:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; 
     P ls ts m ws;
     \<And>ls ts m ws t ta ls' ts' m' ws'. \<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; P ls ts m ws \<rbrakk> \<Longrightarrow> P ls' ts' m' ws' \<rbrakk>
  \<Longrightarrow> P ls' ts' m' ws'"
apply(drule RedT_lift_preserveD[where P="(\<lambda>(ls, (ts, m), ws). P ls ts m ws)"])
by(auto)

lemma RedT_refl [intro, simp]:
  "s -\<triangleright>[]\<rightarrow>* s"
by(rule RedTI)(rule stepify_pred_refl)

lemma redT_has_locks_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t' \<rbrakk> \<Longrightarrow>
  has_locks (ls l) t' = has_locks (ls' l) t'"
by(auto elim!: redT.cases intro: redT_updLs_has_locks[THEN sym, simplified] may_acquire_all_has_locks_acquire_locks[symmetric])

lemma redT_has_lock_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t' \<rbrakk>
  \<Longrightarrow> has_lock (ls' l) t' = has_lock (ls l) t'"
by(auto simp add: redT_has_locks_inv)

lemma redT_ts_Some_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t'; ts t' = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> ts' t' = \<lfloor>x\<rfloor>"
by(auto elim!: redT.cases simp: redT_updTs_upd[THEN sym] intro: redT_updTs_Some)

lemma redT_new_thread_common:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; NewThread t' x m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m'' = m'"
by(auto elim!: redT.cases elim: thread_oks_commonD[THEN sym])

lemma redT_new_thread:
  "\<lbrakk> s -t'\<triangleright>ta\<rightarrow> s'; thr s' t = \<lfloor>(x, w)\<rfloor>; thr s t = None \<rbrakk>
  \<Longrightarrow> NewThread t x (shr s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> w = no_wait_locks"
proof(induct rule: redT_elims)
  case (normal X X')
  from `thr s t' = \<lfloor>(X, no_wait_locks)\<rfloor>` `thr s t = None`
  have "t' \<noteq> t" by auto
  with `thr s' = redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t' \<mapsto> (X', redT_updLns (locks s) t' no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))`
    `thr s' t = \<lfloor>(x, w)\<rfloor>`
  have "redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>(x, w)\<rfloor>" by(auto)
  thm redT_updTs_new_thread
  with `thr s t = None` `thread_oks (thr s) (shr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>`
  show ?case by -(rule redT_updTs_new_thread)
next
  case acquire
  thus ?thesis by(auto split: split_if_asm)
qed

lemma redT_thread_not_disappear:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; ts' t' = None\<rbrakk> \<Longrightarrow> ts t' = None"
apply(cases "t \<noteq> t'")
 apply(erule redT_elims4)
  apply(clarsimp)
  apply(erule redT_updTs_None)
 apply(clarsimp)
apply(auto elim!: redT_elims4 simp add: redT_updTs_upd[THEN sym])
done


lemma RedT_thread_not_disappear:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; ts' t' = None\<rbrakk> \<Longrightarrow> ts t' = None"
apply(erule contrapos_pp[where Q="ts' t' = None"])
apply(drule RedT_lift_preserveD4)
 apply(assumption)
apply(erule_tac Q="tsa t' = None" in contrapos_nn)
apply(erule redT_thread_not_disappear)
apply(auto)
done

lemma redT_new_thread_ts_Some:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; NewThread t' x m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> ts' t' = \<lfloor>(x, no_wait_locks)\<rfloor>"
by(erule redT_elims4)(auto dest: thread_oks_new_thread elim: redT_updTs_new_thread_ts)

lemma RedT_new_thread_ts_not_None:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>;
     NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) ttas\<down>) \<rbrakk>
   \<Longrightarrow> ts' t \<noteq> None"
proof(induct rule: RedT_induct4)
  case refl thus ?case by simp
next
  case (step LS TS M WS TTAS LS' TS' M' WS' T TA LS'' TS'' M'' WS'')
  note Red = `\<langle>LS, (TS, M), WS\<rangle> -\<triangleright>TTAS\<rightarrow>* \<langle>LS', (TS', M'), WS'\<rangle>`
  note IH = `NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) TTAS\<down>) \<Longrightarrow> TS' t \<noteq> None`
  note red = `\<langle>LS', (TS', M'), WS'\<rangle> -T\<triangleright>TA\<rightarrow> \<langle>LS'', (TS'', M''), WS''\<rangle>`
  note ins = `NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) (TTAS @ [(T, TA)])\<down>)`
  show ?case
  proof(cases "NewThread t x m'' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>")
    case True
    moreover
    with red have "m'' = M''" 
      by(auto elim: redT_new_thread_common) 
    ultimately show ?thesis using red
      by(auto dest!: redT_new_thread_ts_Some)
  next
    case False
    hence "NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) TTAS\<down>)" using ins by(auto)
    hence "TS' t \<noteq> None" by -(rule IH)
    with red show ?thesis
      by -(erule contrapos_nn, erule redT_thread_not_disappear)
  qed
qed

lemma redT_preserves_lock_thread_ok:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; lock_thread_ok (locks s) (thr s) \<rbrakk> \<Longrightarrow> lock_thread_ok (locks s') (thr s')"
by(auto elim!: redT_elims intro: redT_upds_preserves_lock_thread_ok acquire_all_preserves_lock_thread_ok)

lemma RedT_preserves_lock_thread_ok:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; lock_thread_ok (locks s) (thr s) \<rbrakk> \<Longrightarrow> lock_thread_ok (locks s') (thr s')"
apply(erule RedT_lift_preserveD, assumption)
by(erule redT_preserves_lock_thread_ok)

lemma RedT_newThread_unique:
  assumes red: "\<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>"
  and ts't: "ts' t = \<lfloor>(x, w)\<rfloor>"
  and tst: "ts t = None"
  shows "\<exists>!n. n < length ttas \<and> (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (ttas!n))))"
using prems
proof(induct arbitrary: x w rule: RedT_induct4)
  case refl thus ?case by auto
next
  case (step LS TS M WS TTAS LS' TS' M' WS' T TA LS'' TS'' M'' WS'' X W)
  note RedT = `\<langle>LS, (TS, M), WS\<rangle> -\<triangleright>TTAS\<rightarrow>* \<langle>LS', (TS', M'), WS'\<rangle>`
  note IH = `\<And>x w. \<lbrakk>TS' t = \<lfloor>(x, w)\<rfloor>; TS t = None\<rbrakk> 
             \<Longrightarrow> \<exists>!n. n < length TTAS \<and> (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n))))`
  note red = `\<langle>LS', (TS', M'), WS'\<rangle> -T\<triangleright>TA\<rightarrow> \<langle>LS'', (TS'', M''), WS''\<rangle>`
  note ts''t = `TS'' t = \<lfloor>(X, W)\<rfloor>`
  note tst = `TS t = None`
  show ?case
  proof(cases "TS' t")
    case None
    note ts't = `TS' t = None`
    with ts''t red have ta: "NewThread t X M'' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>"
      by (auto dest: redT_new_thread)
    show ?thesis
    proof(rule ex1I)
      show "length TTAS < length (TTAS @ [(T, TA)]) \<and>
	    (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! length TTAS))))"
	using ta by auto
    next
      fix n'
      assume "n' < length (TTAS @ [(T, TA)]) \<and>
	      (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n'))))"
      hence n'l: "n' < length (TTAS @ [(T, TA)])" 
	and blubb: "\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n')))" 
	by auto
      from blubb obtain m' x'
	where e'x': "NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n')))"
	by blast
      { assume "n' < length TTAS"
	with e'x' have "NewThread t x' m' \<in> set (\<down>map (thr_a \<circ> snd) TTAS\<down>)"
	  apply(simp add: nth_append)
	  apply(erule_tac x="TTAS ! n'" in bexI)
	  by auto
	hence "TS' t \<noteq> None" using RedT by -(erule RedT_new_thread_ts_not_None)
	with ts't have False by simp }
      thus "n' = length TTAS" using n'l by(simp, arith)
    qed
  next
    fix a
    assume "TS' t = \<lfloor>a\<rfloor>"
    obtain x w where [simp]: "a = (x, w)" by(cases a, auto)
    with `TS' t = \<lfloor>a\<rfloor>` have e'x': "TS' t = \<lfloor>(x, w)\<rfloor>" by simp
    with tst have "\<exists>!n. n < length TTAS \<and> (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n))))"
      by -(rule IH)
    then obtain n
      where nl: "n < length TTAS"
      and exe'x': "\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n)))"
      and unique: "\<forall>n'. n' < length TTAS \<and> (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n'))))
                        \<longrightarrow> n' = n"
      by(blast elim: ex1E)
    show ?thesis
    proof(rule ex1I)
      show "n < length (TTAS @ [(T, TA)]) \<and>
	    (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n))))"
	using nl exe'x' by(simp add: nth_append)
    next
      fix n'
      assume "n' < length (TTAS @ [(T, TA)]) \<and>
	      (\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n'))))"
      hence n'l: "n' < length (TTAS @ [(T, TA)])"
	and ex'e'x': "\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd ((TTAS @ [(T, TA)]) ! n')))"
	by auto
      { assume "n' = length TTAS"
	with ex'e'x' have "\<exists>x' m'. NewThread t x' m' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>"
	  by(auto simp add: nth_append)
	then obtain m'' x''
	  where "NewThread t x'' m'' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>" by blast
	with red have "TS' t = None"
	  by -(erule redT.cases, auto elim: thread_oks_new_thread)
	with e'x' have False by auto }
      moreover
      { assume "n' < length TTAS"
	moreover
	with ex'e'x' have "\<exists>x' m'. NewThread t x' m' \<in> set (thr_a (snd (TTAS ! n')))"
	  by(simp add: nth_append)
	ultimately have "n' = n" using unique by(force) }
      ultimately show "n' = n" using n'l apply(auto) by(arith)
    qed
  qed
qed

end (* locale multithreaded *)

end 
