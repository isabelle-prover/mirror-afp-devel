(*  Title:      JinjaThreads/J/Threaded.thy
    Author:     Andreas Lochbihler
*)

theory Threaded
imports SmallStep "../Framework/FWLiftingSem" JWellForm "../Common/ConformThreaded"
begin


abbreviation final_expr :: "expr \<times> locals \<Rightarrow> bool"where
  "final_expr \<equiv> \<lambda>(e, x). final e"


abbreviation
  mred :: "J_prog \<Rightarrow> (expr \<times> locals) \<times> heap \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) thread_action \<Rightarrow> (expr \<times> locals) \<times> heap \<Rightarrow> bool"
where
  "mred P \<equiv> (\<lambda>((e, l), h)  ta ((e', l'), h'). P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>)"


interpretation red_mthr!: multithreaded "final_expr" "mred P" .

lemmas red_mthr_redT_elims4 = multithreaded.redT_elims4[where r="mred P", consumes 1, case_names normal acquire]

abbreviation
  mredT :: "J_prog \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state \<Rightarrow> (thread_id \<times> (addr,thread_id,expr \<times> locals,heap,addr) thread_action) \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state \<Rightarrow> bool"
where
  "mredT P \<equiv> multithreaded.redT final_expr (mred P)"

abbreviation
  mredT_syntax1 :: "J_prog \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state
                  \<Rightarrow> thread_id \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) thread_action
                  \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow> _" [50,0,0,0,50] 80)
where
  "mredT_syntax1 P s t ta s' \<equiv> mredT P s (t, ta) s'"

abbreviation
  mredT_syntax2 :: "J_prog \<Rightarrow> (addr,thread_id) locks \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<times> heap \<Rightarrow> (addr,thread_id) wait_sets
                  \<Rightarrow> thread_id \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) thread_action
                  \<Rightarrow> (addr,thread_id) locks \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<times> heap \<Rightarrow> (addr,thread_id) wait_sets \<Rightarrow> bool"
                    ("_ \<turnstile> \<langle>_, _, _\<rangle> -_\<triangleright>_\<rightarrow> \<langle>_, _, _\<rangle>" [50,0,0,0,0,0,0,0,0] 80)
where
  "P \<turnstile> \<langle>ls, tsm, ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', tsm', ws'\<rangle> \<equiv> P \<turnstile> (ls, tsm, ws) -t\<triangleright>ta\<rightarrow> (ls', tsm', ws')"


abbreviation
  mRedT_syntax1 :: "J_prog \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state
                  \<Rightarrow> (thread_id \<times> (addr,thread_id,expr \<times> locals,heap,addr) thread_action) list
                  \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>* s' \<equiv> multithreaded.RedT final_expr (mred P) s ttas s'"

abbreviation
  mRedT_syntax2 :: "J_prog \<Rightarrow> (addr,thread_id) locks \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<times> heap \<Rightarrow> (addr,thread_id) wait_sets
                  \<Rightarrow> (thread_id \<times> (addr,thread_id,expr \<times> locals,heap,addr) thread_action) list
                  \<Rightarrow> (addr,thread_id) locks \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<times> heap \<Rightarrow> (addr,thread_id) wait_sets \<Rightarrow> bool"
                    ("_ \<turnstile> \<langle>_, _, _\<rangle> -\<triangleright>_\<rightarrow>* \<langle>_, _, _\<rangle>" [50,0,0,0,0,0,0,0] 80)
where
  "P \<turnstile> \<langle>ls, tsm, ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', tsm', ws'\<rangle> \<equiv> P \<turnstile> (ls, tsm, ws) -\<triangleright>ttas\<rightarrow>* (ls', tsm', ws')"



lemma redT_hext_incr:
  "P \<turnstile> s -t\<triangleright>ta\<rightarrow> s' \<Longrightarrow> hext (shr s) (shr s')"
by(erule multithreaded.redT.cases, auto dest: red_hext_incr)

consts
  sync_ok :: "expr \<Rightarrow> bool"
  sync_oks :: "expr list \<Rightarrow> bool"

primrec
  "sync_ok (new C) = True"
  "sync_ok (newA T\<lfloor>i\<rceil>) = sync_ok i"
  "sync_ok (Cast T e) = sync_ok e"
  "sync_ok (Val v) = True"
  "sync_ok (Var v) = True"
  "sync_ok (e \<guillemotleft>bop\<guillemotright> e') = (sync_ok e \<and> sync_ok e' \<and> ((\<exists>ad. expr_locks e' ad > 0) \<longrightarrow> is_val e))"
  "sync_ok (V := e) = sync_ok e"
  "sync_ok (a\<lfloor>i\<rceil>) = (sync_ok a \<and> sync_ok i \<and> ((\<exists>ad. expr_locks i ad > 0) \<longrightarrow> is_val a))"
  "sync_ok (a\<lfloor>i\<rceil> := e) = (sync_ok a \<and> sync_ok i \<and> sync_ok e \<and> ((\<exists>ad. expr_locks i ad > 0) \<longrightarrow> is_val a) \<and> ((\<exists>ad. expr_locks e ad > 0) \<longrightarrow> is_val a \<and> is_val i))"
  "sync_ok (e\<bullet>F{D}) = sync_ok e"
  "sync_ok (e\<bullet>F{D} := e') = (sync_ok e \<and> sync_ok e' \<and> ((\<exists>ad. expr_locks e' ad > 0) \<longrightarrow> is_val e))"
  "sync_ok (e\<bullet>m(pns)) = (sync_ok e \<and> sync_oks pns \<and> ((\<exists>ad. expr_lockss pns ad > 0) \<longrightarrow> is_val e))"
  "sync_ok ({V : T; e}) = sync_ok e"
  "sync_ok (sync(o') e) = (sync_ok o' \<and> (\<forall>ad. expr_locks e ad = 0))"
  "sync_ok (insync(a) e) = sync_ok e"
  "sync_ok (e;;e') = (sync_ok e \<and> sync_ok e' \<and> ((\<exists>ad. expr_locks e' ad > 0) \<longrightarrow> is_val e \<or> (\<exists>V v. e = V := Val v)))"
  "sync_ok (if (b) e else e') = (sync_ok b \<and> (\<forall>ad. expr_locks e ad = 0) \<and> (\<forall>ad. expr_locks e' ad = 0))"
  "sync_ok (while (b) e) = ((\<forall>ad. expr_locks b ad = 0) \<and> (\<forall>ad. expr_locks e ad = 0))"
  "sync_ok (throw e) = sync_ok e"
  "sync_ok (try e catch(C v) e') = (sync_ok e \<and> sync_ok e' \<and> (\<forall>ad. expr_locks e' ad = 0))"
  "sync_oks [] = True"
  "sync_oks (x # xs) = (sync_ok x \<and> sync_oks xs \<and> ((\<exists>ad. expr_lockss xs ad > 0) \<longrightarrow> is_val x))"

lemma sync_oks_append [simp]: "sync_oks (xs @ ys) \<longleftrightarrow> sync_oks xs \<and> sync_oks ys \<and> ((\<exists>ad. expr_lockss ys ad > 0) \<longrightarrow> (\<exists>vs. xs = map Val vs))"
apply(induct xs)
 apply(simp)
apply(auto)
apply(rule_tac x="v # vs" in exI) 
apply(simp)
done


lemma expr_locks_sync_ok: "(\<And>ad. expr_locks e ad = 0) \<Longrightarrow> sync_ok e"
  and expr_lockss_sync_oks: "(\<And>ad. expr_lockss es ad = 0) \<Longrightarrow> sync_oks es"
proof(induct e and es)
  case (InSynchronized a e)
  { fix ad
    from `expr_locks (insync(a) e) ad = 0`
    have "expr_locks e ad = 0" by(simp split: split_if_asm) }
  with `(\<And>ad. expr_locks e ad = 0) \<Longrightarrow> sync_ok e`
  show ?case by(simp)
qed(fastsimp)+

lemma red_preserve_sync_ok:
  assumes wf: "wf_J_prog P"
  shows "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> sync_ok e'"
proof(induct rule: red.induct)
  prefer 37
  case (RedCall s a C fs M Ts T pns body D vs)
  from wf `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
  have "wf_mdecl wf_J_mdecl P D (M,Ts,T,pns,body)"
    by(rule sees_wf_mdecl)
  then obtain T where "P,[this\<mapsto>Class D,pns[\<mapsto>]Ts] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
  with `length vs = length pns` `length Ts = length pns` 
  have "expr_locks (blocks (pns, Ts, vs, body)) = (\<lambda>ad. 0)"
    by-(rule expr_locks_blocks)
  thus ?case by(auto intro: expr_locks_sync_ok)
next prefer 56
  case (SeqRed e s ta e' s' e2)
  thus ?case by(auto elim: red_cases)
qed(fastsimp intro: expr_locks_sync_ok)+

lemma expr_locks_new_thread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t (e'', x'') h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> expr_locks e'' = (\<lambda>ad. 0)"
by(induct rule: red.induct)(auto)

lemma red_new_thread_sync_ok:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> sync_ok e''"
by(auto dest!: expr_locks_new_thread intro: expr_locks_sync_ok)

abbreviation
  sync_es_ok :: "(addr,thread_id,expr\<times>locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "sync_es_ok \<equiv> ts_ok (\<lambda>(e, x) m. sync_ok e)"

lemma lifting_wf_sync_ok: "wf_J_prog P \<Longrightarrow> lifting_wf (mred P) (\<lambda>(e, x) m. sync_ok e)"
proof qed (auto intro: red_preserve_sync_ok red_new_thread_sync_ok)

lemma redT_preserve_sync_ok:
  assumes red: "P \<turnstile> s -t\<triangleright>ta\<rightarrow> s'"
  shows "\<lbrakk> wf_J_prog P; sync_es_ok (thr s) (shr s) \<rbrakk> \<Longrightarrow> sync_es_ok (thr s') (shr s')"
by(rule lifting_wf.redT_preserves[OF lifting_wf_sync_ok red])

lemmas RedT_preserves_sync_ok = lifting_wf.RedT_preserves[OF lifting_wf_sync_ok]


definition lock_ok :: "(addr,thread_id) locks \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<Rightarrow> bool" where
  "lock_ok ls ts \<equiv> \<forall>t. (case (ts t) of None    \<Rightarrow> (\<forall>l. has_locks (ls l) t = 0)
                                     | \<lfloor>((e, x), ln)\<rfloor> \<Rightarrow> (\<forall>l. has_locks (ls l) t + ln l = expr_locks e l))"

lemma lock_okI:
  "\<lbrakk> \<And>t l. ts t = None \<Longrightarrow> has_locks (ls l) t = 0; \<And>t e x ln l. ts t = \<lfloor>((e, x), ln)\<rfloor> \<Longrightarrow> has_locks (ls l) t + ln l= expr_locks e l \<rbrakk> \<Longrightarrow> lock_ok ls ts"
apply(fastsimp simp add: lock_ok_def)
done

lemma lock_okE:
  "\<lbrakk> lock_ok ls ts;
     \<forall>t. ts t = None \<longrightarrow> (\<forall>l. has_locks (ls l) t = 0) \<Longrightarrow> Q;
     \<forall>t e x ln. ts t = \<lfloor>((e, x), ln)\<rfloor> \<longrightarrow> (\<forall>l. has_locks (ls l) t + ln l = expr_locks e l) \<Longrightarrow> Q \<rbrakk>
  \<Longrightarrow> Q"
apply(fastsimp simp add: lock_ok_def)
done

lemma lock_okD1:
  "\<lbrakk> lock_ok ls ts; ts t = None \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls l) t = 0"
apply(simp add: lock_ok_def)
apply(erule_tac x="t" in allE)
apply(auto)
done

lemma lock_okD2:
  "\<lbrakk> lock_ok ls ts; ts t = \<lfloor>((e, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls l) t + ln l= expr_locks e l"
apply(fastsimp simp add: lock_ok_def)
done

lemma lock_ok_lock_thread_ok:
  assumes lock: "lock_ok ls ts"
  shows "lock_thread_ok ls ts"
proof(rule lock_thread_okI)
  fix l t
  assume lsl: "has_lock (ls l) t"
  show "\<exists>xw. ts t = \<lfloor>xw\<rfloor>"
  proof(cases "ts t")
    case None
    with lock have "has_locks (ls l) t = 0"
      by(auto dest: lock_okD1)
    with lsl show ?thesis by simp
  next
    case (Some a) thus ?thesis by (cases a) simp_all
  qed
qed


fun upd_expr_lock_delta :: "int \<Rightarrow> lock_action \<Rightarrow> int"
where
  "upd_expr_lock_delta i Lock = i + 1"
| "upd_expr_lock_delta i Unlock = i - 1"
| "upd_expr_lock_delta i UnlockFail = i"
| "upd_expr_lock_delta i ReleaseAcquire = i"

fun upd_expr_locks_delta :: "int \<Rightarrow> lock_action list \<Rightarrow> int" where
  "upd_expr_locks_delta n [] = n"
| "upd_expr_locks_delta n (L # Ls) = upd_expr_locks_delta (upd_expr_lock_delta n L) Ls"

lemma upd_expr_locks_delta_append [simp]: "upd_expr_locks_delta n (Ls @ Ls') = upd_expr_locks_delta (upd_expr_locks_delta n Ls) Ls'"
by(induct Ls arbitrary: n, auto)

definition upd_expr_locks :: "(addr \<Rightarrow> int) \<Rightarrow> addr lock_actions \<Rightarrow> addr \<Rightarrow> int"
where "upd_expr_locks els las \<equiv> \<lambda>l. upd_expr_locks_delta (els l) (las l)"

lemma upd_expr_locks_iff [simp]: "upd_expr_locks els las l = upd_expr_locks_delta (els l) (las l)"
by(simp add: upd_expr_locks_def)

lemma upd_expr_locks_append [simp]:
  "upd_expr_locks els (las @@ las') = upd_expr_locks (upd_expr_locks els las) las'"
by(auto simp add: upd_expr_locks_def intro!: ext)


fun upd_expr_lockss :: "(addr \<Rightarrow> int) \<Rightarrow> addr lock_actions list \<Rightarrow> addr \<Rightarrow> int" where
  "upd_expr_lockss els [] = els"
| "upd_expr_lockss els (las#lass) = upd_expr_lockss (upd_expr_locks els las) lass"

lemma upd_expr_lockss_append [simp]:
  "upd_expr_lockss els (lass @ lass') = upd_expr_lockss (upd_expr_lockss els lass) lass'"
by(induct lass arbitrary: els)(auto)

lemma upd_expr_locks_cong:
  "els a = els' a \<Longrightarrow> upd_expr_locks els ta a = upd_expr_locks els' ta a"
by(auto simp add: upd_expr_locks_def)

lemma upd_expr_lockss_cong:
  "els a = els' a \<Longrightarrow> upd_expr_lockss els lass a = upd_expr_lockss els' lass a"
proof(induct lass arbitrary: els els')
  case Nil thus ?case by simp
next
  case (Cons LAS LASS ELS ELS')
  note IH = `\<And>els els'. els a = els' a \<Longrightarrow> upd_expr_lockss els LASS a = upd_expr_lockss els' LASS a`
  note a = `ELS a = ELS' a`
  hence "upd_expr_locks ELS LAS a = upd_expr_locks ELS' LAS a"
    by(rule upd_expr_locks_cong)
  hence "upd_expr_lockss (upd_expr_locks ELS LAS) LASS a = upd_expr_lockss (upd_expr_locks ELS' LAS) LASS a"
    by(rule IH)
  thus ?case by simp
qed

lemma upd_expr_lock_delta_add [simp]:
  "upd_expr_lock_delta (l + l') L = upd_expr_lock_delta l L + l'"
by(cases L, auto)

lemma upd_expr_locks_delta_add [simp]:
  "upd_expr_locks_delta (l + l') Ls = upd_expr_locks_delta l Ls + l'"
by(induct Ls arbitrary: l, auto)

lemma upd_expr_locks_add [simp]:
  "upd_expr_locks (\<lambda>a. x a + y a) las = (\<lambda>a. upd_expr_locks x las a + y a)"
by(auto intro: ext)

lemma upd_expr_lockss_add [simp]:
  "upd_expr_lockss (\<lambda>a. x a + y a) lass = (\<lambda>a. upd_expr_lockss x lass a + y a)"
by(induct lass arbitrary: x, auto simp del: upd_expr_locks_iff)

lemma red_update_expr_locks:
  assumes wf: "wf_J_prog P"
  and red: "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  and sync: "sync_ok e"
  shows "upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"
proof -
  have "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> 
       \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_locks e') ad - (int o expr_locks e) ad)"
  proof(induct rule: red.induct)
    prefer 37
    case (RedCall s a C fs M Ts T pns body D vs)
    from wf `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
    have "wf_mdecl wf_J_mdecl P D (M,Ts,T,pns,body)"
      by(rule sees_wf_mdecl)
    then obtain T where "P,[this\<mapsto>Class D,pns[\<mapsto>]Ts] \<turnstile> body :: T"
      by(auto simp add: wf_mdecl_def)
    hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
    with `length vs = length pns` `length Ts = length pns` 
    have "expr_locks (blocks (pns, Ts, vs, body)) = (\<lambda>ad. 0)"
      by-(rule expr_locks_blocks)
    thus ?case by(auto intro: expr_locks_sync_ok)
  qed(fastsimp simp add: expand_fun_eq)+
  with red sync have "upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_locks e) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'"
    by-(rule ext, simp only: upd_expr_locks_add)
  thus ?thesis by(simp add: o_def)
qed

definition lock_expr_locks_ok :: "thread_id FWState.lock \<Rightarrow> thread_id \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "lock_expr_locks_ok l t n i \<equiv> (i = int (has_locks l t) + int n) \<and> i \<ge> 0"

lemma upd_lock_upd_expr_lock_delta_preserve_lock_expr_locks_ok:
  assumes lao: "lock_action_ok l t L"
  and lelo: "lock_expr_locks_ok l t n i"
  shows "lock_expr_locks_ok (upd_lock l t L) t (upd_threadR n l t L) (upd_expr_lock_delta i L)"
proof -
  from lelo have i: "i \<ge> 0"
    and hl: "i = int (has_locks l t) + int n"
    by(auto simp add: lock_expr_locks_ok_def)
  from lelo
  show ?thesis
  proof(cases L)
    case Lock
    with lao have "may_lock l t" by(simp)
    with hl have "has_locks (lock_lock l t) t = (Suc (has_locks l t))" by(auto)
    with Lock i hl show ?thesis
      by(simp add: lock_expr_locks_ok_def)
  next
    case Unlock
    with lao have "has_lock l t" by simp
    then obtain n' 
      where hl': "has_locks l t = Suc n'"
      by(auto dest: has_lock_has_locks_Suc)
    hence "has_locks (unlock_lock l) t = n'" by simp
    with Unlock i hl hl' show ?thesis
      by(simp add: lock_expr_locks_ok_def)
  qed(auto simp add: lock_expr_locks_ok_def)
qed

lemma upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok:
  "\<lbrakk> lock_actions_ok l t Ls; lock_expr_locks_ok l t n i \<rbrakk>
  \<Longrightarrow> lock_expr_locks_ok (upd_locks l t Ls) t (upd_threadRs n l t Ls) (upd_expr_locks_delta i Ls)"
by(induct Ls arbitrary: l i n)(auto intro: upd_lock_upd_expr_lock_delta_preserve_lock_expr_locks_ok)


definition ls_els_ok :: "(addr,thread_id) locks \<Rightarrow> thread_id \<Rightarrow> (addr \<Rightarrow> nat) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> bool" where
  "ls_els_ok ls t ln els \<equiv> \<forall>l. lock_expr_locks_ok (ls l) t (ln l) (els l)"

lemma ls_els_okI:
  "(\<And>l. lock_expr_locks_ok (ls l) t (ln l) (els l)) \<Longrightarrow> ls_els_ok ls t ln els"
by(auto simp add: ls_els_ok_def)

lemma ls_els_okE:
  "\<lbrakk> ls_els_ok ls t ln els; \<forall>l. lock_expr_locks_ok (ls l) t (ln l) (els l) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: ls_els_ok_def)

lemma ls_els_okD:
  "ls_els_ok ls t ln els \<Longrightarrow> lock_expr_locks_ok (ls l) t (ln l) (els l)"
by(auto simp add: ls_els_ok_def)

lemma redT_updLs_upd_expr_locks_preserves_ls_els_ok:  
 "\<lbrakk> ls_els_ok ls t ln els; lock_ok_las ls t las \<rbrakk> \<Longrightarrow> ls_els_ok (redT_updLs ls t las) t (redT_updLns ls t ln las) (upd_expr_locks els las)"
by(auto intro!: ls_els_okI upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok elim!: ls_els_okE simp add: redT_updLs_def lock_ok_las_def)

lemma sync_ok_redT_updT: 
  assumes "sync_es_ok ts h"
  and nt: "\<And>t e x h''. ta = NewThread t (e, x) h'' \<Longrightarrow> sync_ok e"
  shows "sync_es_ok (redT_updT ts ta) h'"
using assms
proof(cases ta)
  case (NewThread T x m)
  obtain E X where [simp]: "x = (E, X)" by (cases x, auto)
  with NewThread have "sync_ok E" by(simp)(rule nt)
  with NewThread `sync_es_ok ts h` show ?thesis
    apply -
    apply(rule ts_okI)
    apply(case_tac "t=T")
    by(auto dest: ts_okD)
qed(auto intro: ts_okI dest: ts_okD)


lemma sync_ok_redT_updTs: 
  "\<lbrakk> sync_es_ok ts h; \<And>t e x h. NewThread t (e, x) h \<in> set tas \<Longrightarrow> sync_ok e \<rbrakk>
  \<Longrightarrow> sync_es_ok (redT_updTs ts tas) h'"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by(auto intro: ts_okI dest: ts_okD)
next
  case (Cons TA TAS TS)
  note IH = `\<And>ts. \<lbrakk>sync_es_ok ts h; \<And>t e x h''. NewThread t (e, x) h'' \<in> set TAS \<Longrightarrow> sync_ok e\<rbrakk> \<Longrightarrow> sync_es_ok (redT_updTs ts TAS) h'`
  note nt = `\<And>t e x h. NewThread t (e, x) h \<in> set (TA # TAS) \<Longrightarrow> sync_ok e`
  from `sync_es_ok TS h` nt
  have "sync_es_ok (redT_updT TS TA) h"
    by(auto elim!: sync_ok_redT_updT)
  hence "sync_es_ok (redT_updTs (redT_updT TS TA) TAS) h'"
    by(rule IH)(auto intro: nt)
  thus ?case by simp
qed

lemma redT_preserves_lock_ok:
  assumes wf: "wf_J_prog P"
  and "P \<turnstile> s -t\<triangleright>ta\<rightarrow> s'"
  and "lock_ok (locks s) (thr s)"
  and "sync_es_ok (thr s) (shr s)"
  shows "lock_ok (locks s') (thr s')"
proof -
  obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
  obtain ls' ts' h' ws' where s' [simp]: "s' = (ls', (ts', h'), ws')" by(cases s', auto)
  from assms have redT: "P \<turnstile> \<langle>ls, (ts, h), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', h'), ws'\<rangle>"
    and loes: "lock_ok ls ts"
    and aoes: "sync_es_ok ts h" by auto
  from redT have "lock_ok ls' ts'"
  proof(induct rule: red_mthr_redT_elims4)
    case (normal a a')
    moreover obtain e x where "a = (e, x)" by (cases a, auto)
    moreover obtain e' x' where "a' = (e', x')" by (cases a', auto)
    ultimately have P: "P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>"
      and est: "ts t = \<lfloor>((e, x), no_wait_locks)\<rfloor>"
      and lota: "lock_ok_las ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
      and cctta: "thread_oks ts h' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
      and ls': "ls' = redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
      and es': "ts' = redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> ((e', x'), redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))"
      and ws': "ws' = redT_updWs ws t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
      by auto
    from est aoes have aoe: "sync_ok e" by(auto dest: ts_okD)
    from aoe P have aoe': "sync_ok e'" by(auto dest: red_preserve_sync_ok[OF wf])
    from aoes red_new_thread_sync_ok[OF P]
    have "sync_es_ok (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) h'"
      by(rule sync_ok_redT_updTs)
    with aoe' have aoes': "sync_es_ok (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> ((e', x'), redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))) h"
      by(auto intro!: ts_okI dest: ts_okD split: split_if_asm)
    show ?thesis
    proof(rule lock_okI)
      fix t'' l
      assume "ts' t'' = None"
      with es' have "ts t'' = None"
	by(auto split: split_if_asm intro: redT_updTs_None)
      with loes have "has_locks (ls l) t'' = 0"
	by(auto dest: lock_okD1)
      moreover from `ts' t'' = None` es'
      have "t \<noteq> t''" by(simp split: split_if_asm)
      ultimately show "has_locks (ls' l) t'' = 0"
	by(simp add: multithreaded.redT_has_locks_inv[OF redT])
    next
      fix t'' e'' x'' l ln''
      assume ts't'': "ts' t'' = \<lfloor>((e'', x''), ln'')\<rfloor>"
      with aoes' es' have aoe'': "sync_ok e''" by(auto dest: ts_okD)
      show "has_locks (ls' l) t'' + ln'' l = expr_locks e'' l"
      proof(cases "t = t''")
	case True
	note tt'' = `t = t''`
	with ts't'' es' have  e'': "e'' = e'" and x'': "x'' = x'"
	  and ln'': "ln'' = redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
	have "ls_els_ok ls t no_wait_locks (int o expr_locks e)"
	proof(rule ls_els_okI)
	  fix l
	  note lock_okD2[OF loes, OF est]
	  thus "lock_expr_locks_ok (ls l) t 0 ((int \<circ> expr_locks e) l)"
	    by(simp add: lock_expr_locks_ok_def)
	qed
	hence "ls_els_ok (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) t (redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) (upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)"
	  by(rule redT_updLs_upd_expr_locks_preserves_ls_els_ok[OF _ lota])
	hence "ls_els_ok (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) t (redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) (int o expr_locks e')"
	  by(simp only: red_update_expr_locks[OF wf P aoe])
	thus ?thesis using ls' e'' tt'' ln''
	  by(auto dest: ls_els_okD[where l = l] simp: lock_expr_locks_ok_def)
      next
	case False
	note tt'' = `t \<noteq> t''`
	from lota have lao: "lock_actions_ok (ls l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
	  by(simp add: lock_ok_las_def)
	show ?thesis
	proof(cases "ts t''")
	  case None
	  with est ts't'' es' tt'' cctta
	  have "NewThread t'' (e'', x'') h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> ln'' = no_wait_locks"
	    by(auto intro: redT_updTs_new_thread del: conjI)
	  then obtain "NewThread t'' (e'', x'') h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
	    and ln'': "ln'' = no_wait_locks" ..
	  with P have "expr_locks e'' = (\<lambda>ad. 0)"
	    by -(rule expr_locks_new_thread)
	  hence elel: "expr_locks e'' l = 0" by simp
	  from loes None  have "has_locks (ls l) t'' = 0"
	    by(auto dest: lock_okD1)
	  moreover note lock_actions_ok_has_locks_upd_locks_eq_has_locks[OF lao tt''[symmetric]]
	  ultimately have "has_locks (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l) t'' = 0"
	    by(auto simp add: expand_fun_eq)
	  with elel ls' ln'' show ?thesis by(auto)
	next
	  case (Some a)
	  then obtain E X LN where est'': "ts t'' = \<lfloor>((E, X), LN)\<rfloor>" by(cases a, auto)
	  with loes have IH: "has_locks (ls l) t'' + LN l = expr_locks E l"
	    by(auto dest: lock_okD2)
	  from est est'' es' tt'' cctta have "ts' t'' = \<lfloor>((E, X), LN)\<rfloor>"
	    apply(simp)
	    apply(rule redT_updTs_Some)
	    by(simp_all)
	  with ts't'' es' have e'': "E = e''" and x'': "X = x''"
	    and ln'': "ln'' = LN" by(simp_all)
	  with lock_actions_ok_has_locks_upd_locks_eq_has_locks[OF lao tt''[symmetric]] IH ls'
	  show ?thesis by(clarsimp simp add: redT_updLs_def expand_fun_eq)
	qed
      qed
    qed
  next
    case (acquire a ln n)
    note [simp] = `ta = \<epsilon>` `ws' = ws` `h' = h`
    obtain e x where [simp]: "a = (e, x)" by (cases a, auto)
    note ls' = `ls' = acquire_all ls t ln`
    from `ts' = ts(t \<mapsto> (a, no_wait_locks))`
    have ts': "ts' = ts(t \<mapsto> ((e, x), no_wait_locks))" by simp
    from `ts t = \<lfloor>(a, ln)\<rfloor>` have tst: "ts t = \<lfloor>((e, x), ln)\<rfloor>" by simp
    show ?thesis
    proof(rule lock_okI)
      fix t'' l
      assume rtutes: "ts' t'' = None"
      with ts' have tst'': "ts t'' = None"
	by(simp split: split_if_asm)
      with tst have tt'': "t \<noteq> t''" by auto
      from tst'' loes have "has_locks (ls l) t'' = 0"
	by(auto dest: lock_okD1)
      thus "has_locks (ls' l) t'' = 0"
	by(simp add: multithreaded.redT_has_locks_inv[OF redT tt''])
    next
      fix t'' e'' x'' ln'' l
      assume ts't'': "ts' t'' = \<lfloor>((e'', x''), ln'')\<rfloor>"
      show "has_locks (ls' l) t'' + ln'' l = expr_locks e'' l"
      proof(cases "t = t''")
	case True
	note [simp] = this
	with ts't'' ts' tst
	have [simp]: "ln'' = no_wait_locks" "e = e''" by auto
	from tst loes have "has_locks (ls l) t + ln l = expr_locks e l"
	  by(auto dest: lock_okD2)
	show ?thesis
	proof(cases "ln l > 0")
	  case True
	  with `may_acquire_all ls t ln` ls' have "may_lock (ls l) t"
	    by(auto elim: may_acquire_allE)
	  with ls'
	  have "has_locks (ls' l) t = has_locks (ls l) t + ln l"
	    by(simp add: has_locks_acquire_locks_conv)
	  with `has_locks (ls l) t + ln l = expr_locks e l`
	  show ?thesis by(simp)
	next
	  case False
	  hence "ln l = 0" by simp
	  with ls' have "has_locks (ls' l) t = has_locks (ls l) t"
	    by(simp)
	  with `has_locks (ls l) t + ln l = expr_locks e l` `ln l = 0`
	  show ?thesis by(simp)
	qed
      next
	case False
	with ts' ts't'' have tst'': "ts t'' = \<lfloor>((e'', x''), ln'')\<rfloor>" by(simp)
	with loes have "has_locks (ls l) t'' + ln'' l = expr_locks e'' l"
	  by(auto dest: lock_okD2)
	show ?thesis
	proof(cases "ln l > 0")
	  case False
	  with `t \<noteq> t''` ls'
	  have "has_locks (ls' l) t'' = has_locks (ls l) t''" by(simp)
	  with `has_locks (ls l) t'' + ln'' l = expr_locks e'' l`
	  show ?thesis by(simp)
	next
	  case True
	  with `may_acquire_all ls t ln` have "may_lock (ls l) t"
	    by(auto elim: may_acquire_allE)
	  with ls' `t \<noteq> t''` have "has_locks (ls' l) t'' = has_locks (ls l) t''"
	    by(simp add: has_locks_acquire_locks_conv')
	  with ls' `has_locks (ls l) t'' + ln'' l = expr_locks e'' l`
	  show ?thesis by(simp)
	qed
      qed
    qed
  qed
  thus ?thesis by simp
qed


lemma RedT_preserves_lock_ok:
  assumes wf: "wf_J_prog P"
  and Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>* s'"
  and ae: "sync_es_ok (thr s) (shr s)"
  and loes: "lock_ok (locks s) (thr s)"
  shows "lock_ok (locks s') (thr s')"
using Red ae loes
proof(induct rule: multithreaded.RedT_induct[where r="mred P", consumes 1, case_names refl step])
  case refl thus ?case by blast
next
  case step thus ?case
    apply -
    apply(erule redT_preserves_lock_ok[OF wf], assumption)
    by(auto dest: RedT_preserves_sync_ok[OF wf])
qed

lemma red_NewThread_Thread_Object:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>C fs. hp s' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> Class C \<le> Class Thread"
by(induct rule: red.induct)(fastsimp)+

lemma redT_NewThread_Thread_Object:
  "\<lbrakk> P \<turnstile> s -t'\<triangleright>ta\<rightarrow> s'; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>C fs. shr s' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> Class C \<le> Class Thread"
by(auto elim!: multithreaded.redT.cases dest:red_NewThread_Thread_Object)

lemma redT_preserves_thread_conf:
  assumes red: "P \<turnstile> s -t'\<triangleright>ta\<rightarrow> s'"
  and tc: "thread_conf P (thr s) (shr s)"
  shows "thread_conf P (thr s') (shr s')"
proof(rule thread_confI)
  fix t xln
  assume tst': "thr s' t = \<lfloor>xln\<rfloor>"
  obtain e x ln where xln [simp]: "xln = ((e, x), ln)" by(cases xln, auto)
  show "\<exists>T. typeof\<^bsub>shr s'\<^esub> (Addr t) = \<lfloor>T\<rfloor> \<and> P \<turnstile> T \<le> Class Thread"
  proof(cases "thr s t")
    case None
    with red tst' have nt: "NewThread t (e, x) (shr s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" 
      and [simp]: "ln = no_wait_locks" by(auto dest: multithreaded.redT_new_thread)
    from red nt obtain C fs where "shr s' t = \<lfloor>Obj C fs\<rfloor>" "P \<turnstile> Class C \<le> Class Thread"
      by(auto dest!: redT_NewThread_Thread_Object)
    thus ?thesis by(clarsimp)
  next
    case (Some Xln)
    with tc obtain T where "typeof\<^bsub>shr s\<^esub> (Addr t) = \<lfloor>T\<rfloor>" "P \<turnstile> T \<le> Class Thread"
      by(rule thread_confDE)
    moreover from red have "hext (shr s) (shr s')"
      apply -
      by(cases s, cases s')(auto intro: redT_hext_incr)
    ultimately have "typeof\<^bsub>shr s'\<^esub> (Addr t) = \<lfloor>T\<rfloor>"
      by(blast dest: type_of_hext_type_of hext_objarrD)
    with `P \<turnstile> T \<le> Class Thread` show ?thesis by blast
  qed
qed
    
lemma RedT_preserves_thread_conf:
  "\<lbrakk> P \<turnstile> s -\<triangleright>tta\<rightarrow>* s'; thread_conf P (thr s) (shr s) \<rbrakk> \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(rule multithreaded.RedT_lift_preserveD[OF _ _ redT_preserves_thread_conf])

end
