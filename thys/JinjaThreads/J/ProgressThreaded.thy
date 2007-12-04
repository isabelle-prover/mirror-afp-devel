(*  Title:      JinjaThreads/J/ProgressThreaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Multithreaded progress} *}

theory ProgressThreaded 
imports Threaded Progress "../Framework/FWProgress"
begin

lemma final_no_red [elim]:
  "final e \<Longrightarrow> \<not> P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>"
apply(auto elim: red.cases finalE)
done


lemma final_thread_interp: "final_thread (mred P) final_expr"
proof(unfold_locales)
  fix x m ta x' m'
  assume "final_expr x"
  moreover obtain e l where e: "x = (e, l)" by (cases x, auto)
  ultimately have "final e" by simp
  moreover obtain e' l' where e': "(x' :: char list exp \<times> (char list \<rightharpoonup> val)) = (e', l')" by (cases x', auto)
  ultimately show "\<not> ((x,m),ta,x',m') \<in> (mred P)" using e
    by(auto del: notI)
qed


interpretation red_mthr_final: final_thread ["mred P" "final_expr"]
by(rule final_thread_interp)

abbreviation
  def_ass_ts_ok :: "(thread_id,expr \<times> locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "def_ass_ts_ok \<equiv> ts_ok (\<lambda>(e, x) h. \<D> e \<lfloor>dom x\<rfloor>)"

abbreviation
  wt_ts_ok :: "J_prog \<Rightarrow> (thread_id,expr \<times> locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "wt_ts_ok P \<equiv> ts_ok (\<lambda>(e, x) h. \<exists>E T. P,E,h \<turnstile> e : T)"

lemma final_locks: "final e \<Longrightarrow> expr_locks e l = 0"
by(auto elim: finalE)

lemma lock_ok_ls_ts_final_ok:
  assumes lock: "lock_ok ls ts"
  shows "red_mthr_final.ls_ts_final_ok ls ts"
proof(rule final_thread.ls_ts_final_okI[OF final_thread_interp])
  fix l t n
  assume lsl: "ls l = \<lfloor>(t, n)\<rfloor>"
  have "\<exists>e x. ts t = \<lfloor>(e, x)\<rfloor> \<and> has_locks (ls l) t (expr_locks e l)"
  proof(cases "ts t")
    case None
    with lock have "has_locks (ls l) t 0"
      by(auto dest: lock_okD1)
    with lsl have False by(auto elim: has_locksE)
    thus ?thesis by simp
  next
    case (Some a)
    moreover
    then obtain e x where "a = (e, x)" by (cases a, auto)
    moreover
    with lock Some have "has_locks (ls l) t (expr_locks e l)"
      by(auto dest: lock_okD2)
    ultimately show ?thesis by(simp)
  qed
  then obtain e x
    where tst: "ts t = \<lfloor>(e, x)\<rfloor>"
    and hl: "has_locks (ls l) t (expr_locks e l)"
    by blast
  with lsl have "expr_locks e l = Suc n"
    by(auto elim: has_locksE)
  hence "\<not> final e"
    by(auto dest: final_locks elim: finalE)
  with tst show "\<exists>x. ts t = \<lfloor>x\<rfloor> \<and> \<not> final_expr x"
    by(auto)
qed

lemma lock_ok_lock_thread_ok:
  assumes lock: "lock_ok ls ts"
  shows "lock_thread_ok ls ts"
proof(rule lock_thread_okI)
  fix l t n
  assume lsl: "ls l = \<lfloor>(t, n)\<rfloor>"
  show "\<exists>x. ts t = \<lfloor>x\<rfloor>"
  proof(cases "ts t")
    case None
    with lock have "has_locks (ls l) t 0"
      by(auto dest: lock_okD1)
    with lsl have False by(auto elim: has_locksE)
    thus ?thesis by simp
  next
    case (Some a) thus ?thesis by(simp)
  qed
qed


syntax
  can_lock_syntax :: "J_prog \<Rightarrow> expr \<Rightarrow> heap \<times> locals \<Rightarrow> addr set \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>" [50,0,0,0] 81)

translations
  "P \<turnstile> \<langle>e, s\<rangle> L \<wrong>" => "multithreaded.can_lock ((CONST mred) P) (e, snd s) (fst s) L"
  "P \<turnstile> \<langle>e, (h, x)\<rangle> L \<wrong>" <= "multithreaded.can_lock ((CONST mred) P) (e, x) h L"


abbreviation
  must_lock_syntax :: "J_prog \<Rightarrow> expr \<Rightarrow> heap \<times> locals \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>" [50,0,0] 81)
where
  "P \<turnstile> \<langle>e, s\<rangle> \<wrong> \<equiv> multithreaded.must_lock (mred P) (e, snd s) (fst s)"

lemma red_new_thread_heap:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = hp s'"
apply(induct rule: red.induct)
apply(auto)
done

lemma lock_ok_ls_Some_ex_ts_not_final:
  "\<lbrakk> lock_ok ls ts; ls l = \<lfloor>(t, n)\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>e x. ts t = \<lfloor>(e, x)\<rfloor> \<and> \<not> final e"
apply(drule lock_ok_ls_ts_final_ok)
apply(drule final_thread.ls_ts_final_okD[OF final_thread_interp])
by auto

lemma progress_interp: "progress (mred P) final_expr"
by(unfold_locales)

interpretation red_mthr_progress: progress["mred P" "final_expr"]
by(rule progress_interp)



consts
  count_locks :: "expr \<Rightarrow> nat"
  count_lockss :: "expr list \<Rightarrow> nat"

primrec
"count_locks (new C) = 0"
"count_locks (newA T\<lfloor>i\<rceil>) = count_locks i"
"count_locks (Cast T e) = count_locks e"
"count_locks (Val v) = 0"
"count_locks (Var v) = 0"
"count_locks (e \<guillemotleft>bop\<guillemotright> e') = count_locks e + count_locks e'"
"count_locks (V := e) = count_locks e"
"count_locks (a\<lfloor>i\<rceil>) = count_locks a + count_locks i"
"count_locks (a\<lfloor>i\<rceil> := e) = count_locks a + count_locks i + count_locks e"
"count_locks (e\<bullet>F{D}) = count_locks e"
"count_locks (e\<bullet>F{D} := e') = count_locks e + count_locks e'"
"count_locks (e\<bullet>m(pns)) = count_locks e + count_lockss pns"
"count_locks ({V : T; e}) = count_locks e"
"count_locks (sync(o') e) = count_locks o' + count_locks e + (if lock_granted(o') then 1 else 0)"
"count_locks (e;;e') = count_locks e + count_locks e'"
"count_locks (if (b) e else e') = count_locks b + count_locks e + count_locks e'"
"count_locks (while (b) e) = count_locks b + count_locks e"
"count_locks (throw e) = count_locks e"
"count_locks (try e catch(C v) e') = count_locks e + count_locks e'"
"count_lockss [] = 0"
"count_lockss (x # xs) = count_locks x + count_lockss xs"

lemma count_locks_append [simp]:
  "count_lockss (es @ es') = count_lockss es + count_lockss es'"
apply(induct es, auto)
done

lemma red_wf_progress:
  "\<lbrakk>wwf_J_prog P; wt_ts_ok P ts h; def_ass_ts_ok ts h; P \<turnstile> h \<surd>\<rbrakk>
    \<Longrightarrow> progress.wf_progress (mred P) final_expr ts h"
apply(rule progress.wf_progressI[OF progress_interp])
apply(clarsimp)
apply(drule ts_okD, assumption)+
apply(clarify)
apply(drule red_progress)
apply(assumption)+
by fastsimp

lemma red_no_wait_unlock: "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = []  \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock]"
apply(induct rule: red.induct)
apply(fastsimp split: split_if_asm)+
done

lemma red_suspend_has_unlock: "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend l] \<rbrakk> \<Longrightarrow> Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
apply(induct rule: red.induct)
apply(auto)
done

lemma red_wait_at_most_one: "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<forall>wa. \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<noteq> [wa] \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = []"
apply(induct rule: red.induct)
apply(auto)
done

lemma red_lock_at_most_one: "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l' = las; las \<noteq> [] \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>l. [])(l' := las)"
proof(induct arbitrary: las l' rule: red.induct)
  prefer 56
  case (SynchronizedWait e s ta e' s' a was las l')
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<And>las l'. \<lbrakk>\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l' = las; las \<noteq> []\<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>l. [])(l' := las)`
  note ta = `\<lbrace>ta\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l' = las`
  note was = `\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = Suspend a # was`
  note las = `las \<noteq> []`
  from red was have "was = []"
    by(auto dest: red_wait_at_most_one)
  with red was have "Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a)"
    by(auto dest: red_suspend_has_unlock)
  hence "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a \<noteq> []"
    by(cases ta, auto)
  hence "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>l. [])(a := \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a)"
    by(blast intro: IH)
  moreover
  with ta las have "l' = a" 
    apply(cases ta, auto split: split_if_asm)
    apply(unfold expand_fun_eq)
    by(auto)
  ultimately show ?case using las ta
    apply(cases ta, auto intro!: ext split: split_if_asm)
    apply(unfold expand_fun_eq)
    by(erule_tac x="x" in allE, simp)+
qed(fastsimp)+
    

lemma red_unlock_notify: 
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>;
     \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Notify l] \<rbrakk>
  \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]"
apply(induct rule: red.induct)
apply(fastsimp split: split_if_asm)+
done

lemma red_unlock_notifyall:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>;
     \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [NotifyAll l] \<rbrakk>
  \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]"
apply(induct rule: red.induct)
apply(fastsimp split: split_if_asm)+
done

lemma red_unlock_wait: 
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
    addr_ok e;
    \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend l] \<rbrakk>
  \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ replicate (expr_locks e l) Unlock"
proof(induct rule: red.induct)
  prefer 56
  case (SynchronizedWait e s ta e' s' a was)
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<lbrakk>addr_ok e; \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend l]\<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ replicate (expr_locks e l) Unlock`
  note was = `\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = Suspend a # was`
  note aoe = `addr_ok (sync(locked(a)) e)`
  hence "addr_ok e" by simp
  moreover
  note ta = `\<lbrace>ta\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>w\<^esub> = [Suspend l]`
  hence "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend l]"
    by(cases ta, auto)
  ultimately have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ replicate (expr_locks e l) Unlock"
    by -(rule IH)
  moreover from was ta have "l = a"
    by(cases ta, auto)
  ultimately show ?case
    by(cases ta, simp add: replicate_app_Cons_same)
next prefer 57
  case (SeqRed e s ta e' s' e2)
  note aoe = `addr_ok (e;; e2)`
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  with `\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend l]` have unl: "Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
    by -(erule red_suspend_has_unlock)
  with red aoe have "\<not> contains_addr e2"
    by(auto elim!: red_cases)
  hence "expr_locks e2 l = 0"
    by(rule contains_addr_expr_locks)
  with SeqRed show ?case
    by(auto)
qed(fastsimp split: split_if_asm simp add: contains_addr_expr_locks contains_addrs_expr_lockss)+

lemma red_unlock_no_wait_expr_locks:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
      addr_ok e;
      Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); 
      \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [] \<rbrakk>
  \<Longrightarrow> expr_locks e l > 0"
apply(induct rule: red.induct)
apply(fastsimp split: split_if_asm)+
done


lemma red_Unlock_Lock_no_lock_ex_UnlockFail:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock];
     expr_locks e l = 0 \<rbrakk>
  \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  prefer 40
  case (RedWait s a arrobj)
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]`
  hence "a = l" by(simp split: split_if_asm)
  with `hp s a = \<lfloor>arrobj\<rfloor>` show ?case
    by(fastsimp intro: RedWaitFail)
next prefer 41
  case (RedNotify s a arrobj)
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>w\<^esub>Notify a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]`
  hence "a = l" by(simp split: split_if_asm)
  with `hp s a = \<lfloor>arrobj\<rfloor>` show ?case
    by(fastsimp intro: RedNotifyFail)
next prefer 42
  case (RedNotifyAll s a arrobj)
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>w\<^esub>NotifyAll a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]`
  hence "a = l" by(simp split: split_if_asm)
  with `hp s a = \<lfloor>arrobj\<rfloor>` show ?case
    by(fastsimp intro: RedNotifyAllFail)
next prefer 44
  case (BlockRedNone e h x V ta e' h' l' T)
  note IH = `\<lbrakk>\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]; expr_locks e l = 0\<rbrakk> \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]` `expr_locks {V:T; e} l = 0` obtain e' s'
    where "P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by fastsimp
  moreover
  then obtain h' x' where "s' = (h', x')" by (cases s', auto)
  ultimately show ?case using `\<not> assigned V e`
    apply(cases "x' V")
     apply(fastsimp intro: red.BlockRedNone)
    by(fastsimp intro: red.BlockRedSome)
next prefer 44
  case (BlockRedSome e h x V ta e' h' l' v T)
  note IH = `\<lbrakk>\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]; expr_locks e l = 0\<rbrakk> \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]` `expr_locks {V:T; e} l = 0` obtain e' s'
    where red: "P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by fastsimp
  moreover
  then obtain h' x' where "s' = (h', x')" by (cases s', auto)
  ultimately show ?case using `\<not> assigned V e`
    apply(cases "x' V")
     apply(fastsimp intro: red.BlockRedNone)
    by(fastsimp intro: red.BlockRedSome)
next prefer 44
  case (InitBlockRed e h x V v ta e' h' x' v' T)
  from `\<lbrakk>\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]; expr_locks e l = 0\<rbrakk> \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
    `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]` `expr_locks {V:T; V:=Val v;; e} l = 0`
  obtain e' s'
    where red: "P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by fastsimp
  moreover
  then obtain h' x' where s': "s' = (h', x')" by (cases s', auto)
  ultimately have "\<exists>v. x' V = \<lfloor>v\<rfloor>"
    by(auto dest!: red_lcl_incr)
  with red s' show ?case
    by(fastsimp intro: red.InitBlockRed)
qed(fastsimp intro: red.intros split: split_if_asm)+

lemma red_UnlockFail_UnlockFail:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); addr_ok e \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
proof(induct rule: red.induct)
  prefer 56
  case (SynchronizedWait e s ta e' s' a was)
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `\<lbrakk>UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); addr_ok e\<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  note taw = `\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = Suspend a # was`
  note aoe = `addr_ok (sync(locked(a)) e)`
  note tal = `UnlockFail \<in> set (\<lbrace>ta\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l)`
  hence "UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
    by(cases ta, auto split: split_if_asm)
  hence tal: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]" using aoe
    by(auto intro: IH simp del: locks_a_def)
  moreover
  from red taw have "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend a]"
    by(auto dest: red_wait_at_most_one)
  with red aoe have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a = [Unlock, Lock] @ replicate (expr_locks e a) Unlock"
    by -(rule red_unlock_wait, auto)
  moreover with tal red have "a = l"
    by(auto dest: red_lock_at_most_one[where l'=l] split: split_if_asm)
  ultimately have False by(auto)
  thus ?case by simp
qed(fastsimp split: split_if_asm)+
  


lemma red_UnlockFail_ex_Unlock:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; addr_ok e; 
     \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail] \<rbrakk>
  \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e, s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e', s'\<rangle>
           \<or> P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub> Notify l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>
           \<or> P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub> NotifyAll l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  prefer 41
  case (RedWaitFail s a arrobj)
  note h = `hp s a = \<lfloor>arrobj\<rfloor>`
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  hence "a = l" by(auto split: split_if_asm)
  with h show ?case
    by -(drule RedWait, fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else split: split_if_asm)
next prefer 42
  case (RedNotifyFail s a arrobj)
  note h = `hp s a = \<lfloor>arrobj\<rfloor>`
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  hence "a = l" by(auto split: split_if_asm)
  with h show ?case
    by -(drule RedNotify, fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else split: split_if_asm)
next prefer 43
  case (RedNotifyAllFail s a arrobj)
  note h = `hp s a = \<lfloor>arrobj\<rfloor>`
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  hence "a = l" by(auto split: split_if_asm)
  with h show ?case
    by -(drule RedNotifyAll, fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else split: split_if_asm)
next prefer 44
  case (BlockRedNone e h x V ta e' h' l' T)
  note IH = `\<lbrakk>addr_ok e; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]\<rbrakk>
             \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
                     \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
                     \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  from `addr_ok {V:T; e}` `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  have "\<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
    by - (rule IH, auto)
  then obtain e' s' 
    where "P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
         \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
         \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by blast
  moreover
  obtain h' x' where "s' = (h', x')" by (cases s', auto)
  moreover note `\<not> assigned V e`
  ultimately show ?case
    apply(cases "lcl s' V")
     apply(fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else intro: red.BlockRedNone)
    apply(fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else intro: red.BlockRedSome)
    done
next prefer 44
  case (BlockRedSome e h x V ta e' h' l' v T)
  note IH = `\<lbrakk>addr_ok e; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]\<rbrakk>
             \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
                     \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
                     \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  from `addr_ok {V:T; e}` `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  have "\<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
    by - (rule IH, auto)
  then obtain e' s' 
    where "P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
         \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
         \<or> P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by blast
  moreover
  obtain h' x' where "s' = (h', x')" by (cases s', auto)
  moreover note `\<not> assigned V e`
  ultimately show ?case
    apply(cases "lcl s' V")
     apply(fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else intro: red.BlockRedNone)
    apply(fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else intro: red.BlockRedSome)
    done
next prefer 44
  case (InitBlockRed e h x V v ta e' h' l' v' T)
  note IH = `\<lbrakk>addr_ok e; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]\<rbrakk>
             \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
                     \<or> P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
                     \<or> P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  from `addr_ok {V:T; V:=Val v;; e}` `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  have "\<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
             \<or> P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
             \<or> P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
    by - (rule IH, auto)
  then obtain e' s' 
    where red: "P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
             \<or> P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
             \<or> P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by blast
  moreover
  obtain h' x' where "s' = (h', x')" by (cases s', auto)
  moreover
  from red have "\<exists>v. lcl s' V = \<lfloor>v\<rfloor>"
    by(auto dest: red_lcl_incr_aux)
  ultimately show ?case
    by(fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else intro: red.InitBlockRed)
next prefer 49
  case (SynchronizedRed2 e s ta e' s' a)
  note IH = `\<lbrakk>addr_ok e; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]\<rbrakk>
             \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle> 
                      \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
                      \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  from `addr_ok (sync(locked(a)) e)` `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  have "\<exists>e' s'. P \<turnstile> \<langle>e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle> 
              \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
    by -(rule IH, auto)
  then obtain e' s'
    where "P \<turnstile> \<langle>e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle> 
         \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
         \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by blast
  thus ?case
  proof(rule disjE3)
    assume red: "P \<turnstile> \<langle>e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>"
    hence "\<exists>e'. P \<turnstile> \<langle>sync(locked(a)) e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks (sync(locked(a)) e) l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>"
    proof(cases "a = l")
      case True
      with red have "P \<turnstile> \<langle>sync(locked(a)) e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<rightarrow> \<langle>sync(addr a) e',s'\<rangle>"
	by -(erule red.SynchronizedWait, simp)
      with True show ?thesis
	apply(simp)
	apply(unfold replicate_app_Cons_same)
	by(fastsimp)
    next
      case False
      with red have "P \<turnstile> \<langle>sync(locked(a)) e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>sync(locked(a)) e',s'\<rangle>"
	by -(erule red.SynchronizedRed2, simp)
      with False show ?thesis
	by(fastsimp)
    qed
    thus ?thesis by blast
  qed(fastsimp intro: red.SynchronizedRed2)+
next prefer 49
  case (SynchronizedWait e s ta e' s' a was)
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  from `\<lbrace>ta\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  have tal: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]" 
    by(cases ta, auto split: split_if_asm)
  note taw = `\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = Suspend a # was`
  with red have "was = []"
    by(auto dest: red_wait_at_most_one)
  with taw have "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend a]" by simp
  with red have "Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a)"
    by(rule red_suspend_has_unlock)
  with tal red have False
    by(auto dest: red_lock_at_most_one[where l'=l] split: split_if_asm)
  thus ?case by simp
next prefer 50
  case (SeqRed e s ta e' s' e2)
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note aoe = `addr_ok (e;; e2)`
  note tal = `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  note IH = `\<lbrakk>addr_ok e; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]\<rbrakk>
             \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle> 
                      \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
                      \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  from aoe tal
  have "\<exists>e' s'. P \<turnstile> \<langle>e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle> 
              \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
    by -(rule IH, auto)
  then obtain e' s'
    where "P \<turnstile> \<langle>e,s\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle> 
         \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
         \<or> P \<turnstile> \<langle>e,s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by blast
  moreover
  from aoe tal red have "expr_locks e2 l = 0"
    by(auto elim: red_cases simp: contains_addr_expr_locks)
  ultimately show ?case
    by(fastsimp intro: red.SeqRed simp add: fun_upd_def if_else_if_else_eq_if_else)
qed(fastsimp intro: red.intros simp add: contains_addr_expr_locks contains_addrs_expr_lockss split: split_if_asm)+
 


  
lemma red_thread_at_most_one:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> [] \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThreadFail] \<or> (\<exists>t e x. \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e, x) (hp s')])"
apply(induct rule: red.induct)
apply(auto)
done


lemma red_NewThreadFail_NewThread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThreadFail] \<rbrakk> \<Longrightarrow> \<exists>e' s' e'' x''. P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread t (e'', x'') (hp s')\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  prefer 47
  case (BlockRedNone e h l V ta e' h' l' T)
  thus ?case
    apply(clarsimp)
    apply(case_tac "b V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next
  prefer 47
  case (BlockRedSome e h l V ta e' h' l' v T)
  thus ?case
    apply(clarsimp)
    apply(case_tac "b V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next
  prefer 47
  case (InitBlockRed e h l V v ta e' h' l' v' T)
  from `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThreadFail]`
    `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThreadFail] \<Longrightarrow> \<exists>e' s' e'' x''. P \<turnstile> \<langle>e,(h, l(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread t (e'', x'') (hp s')\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  obtain e' s' e'' x''
    where red: "P \<turnstile> \<langle>e,(h, l(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread t (e'', x'') (hp s')\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
    by blast
  moreover obtain h' l' where "s' = (h', l')" by (cases s', auto)
  moreover with red have "\<exists>v. l' V = \<lfloor>v\<rfloor>"
    by(auto dest: red_lcl_incr_aux)
  ultimately show ?case
    by(fastsimp intro: red.InitBlockRed)
qed(fastsimp intro: red.intros)+

lemma red_thread_no_other:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> [] \<rbrakk> \<Longrightarrow> ta = (\<lambda>l. [], \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>, [])"
apply(induct rule: red.induct)
apply(auto)
done

lemma red_NewThread_NewThread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') (hp s')] \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread t' (e'', x'') (hp s')\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  prefer 38
  case (RedNewThread s a C fs ta)
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread ta (Var this\<bullet>run([]), [this \<mapsto> Addr a]) (hp s)\<rbrace>\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') (hp s)]`
  hence ta: "ta = t"
    and e'': "e'' = Var this\<bullet>run([])"
    and x'': "x'' = [this \<mapsto> Addr a]" by auto
  with `hp s a = \<lfloor>Obj C fs\<rfloor>` `P \<turnstile> C \<preceq>\<^sup>* Thread` show ?case
    apply(simp del: ta_update_NewThread.simps hp_def fun_upd_apply)
    by(rule red.RedNewThread)
next prefer 55
  case (SynchronizedWait e s ta e' s' a was)
  from `\<lbrace>ta\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') (hp s')]`
  have "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') (hp s')]" by(cases ta, auto)
  with `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>` have "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = []"
    by(auto dest: red_thread_no_other)
  with `\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = Suspend a # was` show ?case by auto
qed(fastsimp intro:red.intros)+

lemma red_NewThread_NewThreadFail:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') m] \<rbrakk> \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThreadFail\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  prefer 47
  case (BlockRedNone e h l V ta e' h' l' T)
  thus ?case
    apply(clarsimp)
    apply(case_tac "b V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next prefer 47
  case (BlockRedSome e h l V ta e' h' l' v T)
  thus ?case
    apply(clarsimp)
    apply(case_tac "b V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next prefer 47
  case (InitBlockRed e h l V v ta e' h' l' v' T)
  then obtain e' s'
    where "P \<turnstile> \<langle>e,(h, l(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThreadFail\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
    by auto
  moreover hence "\<exists>v. lcl s' V = \<lfloor>v\<rfloor>"
    by(auto dest: red_lcl_incr_aux)
  ultimately show ?case
    by(cases s', fastsimp intro: red.InitBlockRed)
qed(fastsimp intro: red.intros)+

lemma red_wf_red_precond: 
  assumes wwf: "wwf_J_prog P"
  and aeos: "addr_es_ok ts m"
  and lockok: "lock_ok ls ts"
  and hconf: "P \<turnstile> m \<surd>"
  shows "multithreaded.wf_red_precond (mred P) ls ts m"
proof(rule multithreaded.wf_red_precondI)
  fix t ex ta e'x' m'
  assume tst: "ts t = \<lfloor>ex\<rfloor>"
  assume "((ex, m), ta, e'x', m') \<in> mred P"
  moreover
  obtain e x
    where ex: "ex = (e, x)" by(cases ex, auto)
  moreover
  obtain e' x'
    where e'x': "e'x' = (e', x')" by (cases e'x', auto)
  ultimately have red: "P \<turnstile> \<langle>e, (m, x)\<rangle> -ta\<rightarrow> \<langle>e', (m', x')\<rangle>" by simp
  from tst aeos ex have aoe: "addr_ok e"
    by(auto dest: ts_okD)
  show "\<exists>ta' e'x' m'. ((ex, m), ta', e'x', m') \<in> mred P \<and> thread_oks ts m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> lock_ok_las' ls t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  proof(cases "thread_oks ts m' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>")
    case True
    note cct = `thread_oks ts m' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>`
    show ?thesis
    proof(cases "lock_ok_las' ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>")
      case True
      moreover
      have "collect_locks' \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
	by(auto intro!: collect_locksI must_acquire_lock_contains_lock elim!: collect_locks'E)
      ultimately show ?thesis using cct red ex e'x'
	by(fastsimp)
    next
      case False
      then obtain l
	where l: "\<not> lock_actions_ok' (ls l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
	by(auto simp add: not_lock_ok_las'_conv)
      hence nlaos: "\<not> lock_actions_ok (ls l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
	and lao': "\<And>xs ys. \<lbrakk> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ Lock # ys; lock_actions_ok (ls l) t xs \<rbrakk> \<Longrightarrow> may_lock (upd_locks (ls l) t xs) t"
	by(auto simp only: not_lock_actions_ok'_conv)
      from nlaos obtain xs L ys
	where tal: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys"
	and loa: "lock_actions_ok (ls l) t xs"
	and nlao: "\<not> lock_action_ok (upd_locks (ls l) t xs) t L"
	by(auto simp only: not_lock_actions_ok_conv)
      from nlao show ?thesis
      proof(rule not_lock_action_okE)
	assume L: "L = Lock"
	  and nml: "\<not> may_lock (upd_locks (ls l) t xs) t"
	with tal loa have False
	  by(auto simp del: locks_a_def dest: lao')
	thus ?thesis by simp
      next
	assume L: "L = Unlock"
	  and nhl: "\<not> has_lock (upd_locks (ls l) t xs) t"
	with tal have unlocktal: "Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
	  by simp
	show ?thesis
	proof(cases "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub>")
	  case Nil
	  with red unlocktal have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock]"
	    by(rule red_no_wait_unlock)
	  with tal L have xs: "xs = []" and ys: "ys = []"
	    by(auto simp add: append_eq_Cons_conv)
	  with nhl have nhl: "\<not> has_lock (ls l) t"
	    by simp
	  with tst ex have "expr_locks e l = 0"
	    by(auto intro: lock_ok_not_has_lock_expr_locks[OF lockok])
	  moreover
	  from aoe red unlocktal Nil have "expr_locks e l > 0"
	    by -(rule red_unlock_no_wait_expr_locks)
	  ultimately show ?thesis by simp
	next
	  case (Cons wa was)
	  with red have was: "was = []"
	    by(auto dest: red_wait_at_most_one)
	  with Cons have taw: "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [wa]" by simp
	  show ?thesis
	  proof(cases wa)
	    case (Suspend w)
	    with red taw have "Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> w)"
	      by(auto dest: red_suspend_has_unlock)
	    with red tal L have w: "w = l"
	      by(auto dest: red_lock_at_most_one[where l'=l] split: split_if_asm)
	    with taw Suspend have tal': "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ replicate (expr_locks e l) Unlock"
	      by - (rule red_unlock_wait[OF red aoe], cases ta, simp)
	    show ?thesis
	    proof(cases xs)
	      case Nil
	      with nhl have nhl: "\<not> has_lock (ls l) t" by(simp)
	      with tst ex have elel: "expr_locks e l = 0"
		by(auto intro: lock_ok_not_has_lock_expr_locks[OF lockok])
	      moreover
	      with tal' have tal': "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]" by simp
	      ultimately have "\<exists>e' s'. P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" using red
		by -(rule red_Unlock_Lock_no_lock_ex_UnlockFail)
	      then obtain e' s'
		where red': "P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" by blast
	      obtain m' x' where s': "s' = (m', x')" by (cases s', auto)
	      with red' ex nhl show ?thesis
		by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def
                            elim!: collect_locks'E split: if_splits)
	    next
	      case (Cons X XS)
	      with tal L tal' obtain XS'
		where XS: "XS = Lock # XS'"
		and X: "X = Unlock"
		by(cases XS, auto)
	      with tal L tal' Cons have XS': "XS' @ Unlock # ys = replicate (expr_locks e l) Unlock"
		by(auto)
	      hence elel: "expr_locks e l > 0"
		by(cases "expr_locks e l", auto)
	      then obtain n where n: "expr_locks e l = Suc n" by(cases "expr_locks e l", auto)
	      moreover
	      from tst ex lockok have "has_locks (ls l) t (expr_locks e l)"
		by(auto dest!: lock_okD2)
	      moreover
	      with n have "lock_lock (unlock_lock (ls l)) t = ls l"
		by(auto intro: has_lock_lock_lock_unlock_lock_id has_locks_Suc_has_lock)
	      ultimately have "lock_actions_ok (ls l) t (Unlock # Lock # replicate (expr_locks e l) Unlock)"
		apply(auto)
		   apply(erule has_locks_Suc_has_lock)
		  apply(fastsimp intro: may_lock_t_may_lock_unlock_lock_t has_locks_Suc_has_lock has_lock_may_lock)
		 apply(cases n, (fastsimp elim!: has_locksE intro!: has_lockI)+)
		by(fast intro: has_locks_lock_actions_ok_replicate_Unlock has_locks_Suc_unlock_lock_has_locks)
	      with tal Cons X XS L XS'[THEN sym] have "lock_action_ok (upd_locks (ls l) t xs) t L"
		by(auto)
	      with nlao show ?thesis by contradiction
	    qed
	  next
	    case (Notify w)
	    with red taw have taw: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> w = [Unlock, Lock]"
	      by(auto intro: red_unlock_notify simp del: locks_a_def)
	    with red tal L have w: "w = l"
	      by(auto dest: red_lock_at_most_one[where l'=l] split: split_if_asm)
	    with taw tal L have xs: "xs = []"
	      by(cases ta, auto simp add: Cons_eq_append_conv)
	    with nhl have nhl: "\<not> has_lock (ls l) t" by simp
	    with tst ex have elel: "expr_locks e l = 0"
	      by(auto intro: lock_ok_not_has_lock_expr_locks[OF lockok])
	    with taw w have "\<exists>e' s'. P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" using red
	      by(blast intro!: red_Unlock_Lock_no_lock_ex_UnlockFail)
	    then obtain e' s'
		where red': "P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" by blast
	    obtain m' x' where s': "s' = (m', x')" by (cases s', auto)
	    with red' ex nhl show ?thesis
	      by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def
                          elim!: collect_locks'E split: if_splits)
	  next
	    case (NotifyAll w)
	    with red taw have taw: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> w = [Unlock, Lock]"
	      by(auto intro: red_unlock_notifyall simp del: locks_a_def)
	    with red tal L have w: "w = l"
	      by(auto dest: red_lock_at_most_one[where l'=l] split: split_if_asm)
	    with taw tal L have xs: "xs = []"
	      by(cases ta, auto simp add: Cons_eq_append_conv)
	    with nhl have nhl: "\<not> has_lock (ls l) t" by simp
	    with tst ex have elel: "expr_locks e l = 0"
	      by(auto intro: lock_ok_not_has_lock_expr_locks[OF lockok])
	    with taw w have "\<exists>e' s'. P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" using red
	      by(blast intro!: red_Unlock_Lock_no_lock_ex_UnlockFail)
	    then obtain e' s'
		where red': "P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" by blast
	    obtain m' x' where s': "s' = (m', x')" by (cases s', auto)
	    with red' ex nhl show ?thesis
	      by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def
                          elim!: collect_locks'E split: if_splits)
	  qed
	qed
      next
	assume L: "L = UnlockFail"
	assume hl: "has_lock (upd_locks (ls l) t xs) t"
	from L red tal aoe have tal': "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
	  by -(erule red_UnlockFail_UnlockFail, auto)
	from L tal tal' have xs: "xs = []" and ys: "ys = []"
	  by(auto simp add: append_eq_Cons_conv)
	with hl have hl: "has_lock (ls l) t" by simp
	hence laoul: "lock_actions_ok (ls l) t [Unlock, Lock]"
	  by(auto intro: may_lock_t_may_lock_unlock_lock_t has_lock_may_lock)
	hence laoul': "lock_ok_las' ls t ((\<lambda>l. [])(l := [Unlock, Lock]))"
	  by(auto simp add: lock_ok_las'_def lock_ok_las_def lock_actions_ok'_def)
	from hl lockok tst ex have hls: "has_locks (ls l) t (expr_locks e l)"
	  by(auto dest: lock_okD2)
	hence laorep: "lock_actions_ok (ls l) t (replicate (expr_locks e l) Unlock)"
	  by(rule has_locks_lock_actions_ok_replicate_Unlock)
	from hl obtain n where n: "has_locks (ls l) t (Suc n)"
	  by(auto simp add: has_lock_has_locks_conv)
	have cl: "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
	    by(auto intro: collect_locksI elim!: collect_locks'E split: if_splits)
	from red_UnlockFail_ex_Unlock[OF red aoe tal']
	obtain e' s'
	  where "P \<turnstile> \<langle>e,(m, x)\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by blast
	thus ?thesis
	proof(rule disjE3)
	  assume red': "P \<turnstile> \<langle>e,(m, x)\<rangle> -((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock), [], [Suspend l])\<rightarrow> \<langle>e',s'\<rangle>"
	  with hl laorep have "lock_ok_las ls t ((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock))"
	    by(auto simp add: lock_ok_las_def has_lock_lock_lock_unlock_lock_id intro: may_lock_t_may_lock_unlock_lock_t has_lock_may_lock)
	  hence "lock_ok_las' ls t ((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock))"
	    by(auto simp add: lock_ok_las'_def lock_ok_las_def lock_actions_ok'_def)
	  moreover have "collect_locks' ((\<lambda>l. [])(l := Unlock # Lock # replicate (expr_locks e l) Unlock)) \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
	    by(auto intro: collect_locksI elim!: collect_locks'E split: if_splits)
	  ultimately show ?thesis using ex red'
	    by(cases s', fastsimp)
	next
	  assume "P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
	  with laoul' cl ex show ?thesis
	    by(cases s', fastsimp)
	next
	  assume "P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
	  with laoul' cl ex show ?thesis
	    by(cases s', fastsimp)
	qed
      qed
    qed
  next
    case False
    then obtain xs TA ys
      where tat: "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys"
      and tok: "thread_oks ts m' xs"
      and ntok: "\<not> thread_ok (redT_updTs ts xs) m' TA"
      by(auto simp add: not_thread_oks_conv)
    from tat red have tat': "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThreadFail] \<or> (\<exists>t e x. \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e, x) m'])"
      by(auto dest: red_thread_at_most_one)
    with tat have xs: "xs = []" 
      and ys: "ys = []"
      by(auto simp add: append_eq_Cons_conv)
    with ntok have ntok: "\<not> thread_ok ts m' TA" by(simp)
    from tat' show ?thesis
    proof(rule disjE)
      assume tat': "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThreadFail]"
      with tat xs ys have TA: "TA = NewThreadFail" by(simp)
      with ntok obtain t
	where t: "free_thread_id ts t"
	by(auto)
      from tat' red obtain e' s' e'' x''
	where red': "P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread t (e'', x'') (hp s')\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
	by -(drule red_NewThreadFail_NewThread[where t=t], auto)
      obtain h' x' where s': "s' = (h', x')" by (cases s', auto)
      with t red' ex show ?thesis
	by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def elim: collect_locks'E)
    next
      assume "\<exists>t e x. \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e, x) m']"
      then obtain t e'' x''
	where tat': "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') m']" 
	by blast
      with tat xs ys have TA: "TA = NewThread t (e'', x'') m'" by(simp)
      with ntok have "\<not> free_thread_id ts t" by(simp)
      show ?thesis
      proof(cases "\<exists>t. free_thread_id ts t")
	case True
	then obtain t' where t': "free_thread_id ts t'" by blast
	moreover from red tat' e'x' have "P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread t' (e'', x'') m'\<rbrace>\<rightarrow> \<langle>e',(m', x')\<rangle>"
	  by(fastsimp dest: red_NewThread_NewThread)
	ultimately show ?thesis using ex
	  by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def elim: collect_locks'E)
      next
	case False
	from red_NewThread_NewThreadFail[OF red tat'] obtain e' s'
	  where red': "P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThreadFail\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by blast
	moreover obtain h' x' where "s' = (h', x')" by (cases s', auto)
	moreover from False have "thread_oks ts h' \<lbrace>\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThreadFail\<rbrace>\<rbrace>\<^bsub>t\<^esub>"
	  by(auto)
	ultimately show ?thesis using ex
	  by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def elim: collect_locks'E)
      qed
    qed
  qed
qed

lemma red_progressT:
  "\<lbrakk> wwf_J_prog P; wt_ts_ok P (thr s) (shr s); def_ass_ts_ok (thr s) (shr s);
     addr_es_ok (thr s) (shr s); lock_ok (locks s) (thr s);
     thr s t = \<lfloor>(e, x)\<rfloor>; \<not> final e; t \<notin> progress.deadlocked (mred P) final_expr s; P \<turnstile> shr s \<surd> \<rbrakk>
  \<Longrightarrow> \<exists>t ta s'. P \<turnstile> s -t\<triangleright>ta\<rightarrow> s'"
apply(rule progress.redT_progress[OF progress_interp])
     apply(assumption)
    apply(fastsimp)
   apply(assumption)
  apply(rule red_wf_progress)
      apply(assumption)+
 apply(erule lock_ok_lock_thread_ok)
by(rule red_wf_red_precond)


end

