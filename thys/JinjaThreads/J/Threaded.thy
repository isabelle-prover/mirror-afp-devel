(*  Title:      JinjaThreads/J/Threaded.thy
    Author:     Andreas Lochbihler
*)

header{* The source language as an instance of the framework *}

theory Threaded imports SmallStep "../Framework/FWLiftingSem" JWellForm "../Common/ConformThreaded" begin


abbreviation final_expr :: "expr \<times> locals \<Rightarrow> bool"where
  "final_expr \<equiv> \<lambda>(e, x). final e"

abbreviation
  mred :: "J_prog \<Rightarrow> (expr \<times> locals) \<times> heap \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) thread_action \<Rightarrow> (expr \<times> locals) \<times> heap \<Rightarrow> bool"
where
  "mred P \<equiv> (\<lambda>((e, l), h)  ta ((e', l'), h'). P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>)"

lemma red_new_thread_heap:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' ex'' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = hp s'"
  and reds_new_thread_heap:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' ex'' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = hp s'"
apply(induct rule: red_reds.inducts)
apply(fastsimp dest: red_ext_new_thread_heap)+
done

lemma red_mthr: "multithreaded (mred P)"
by(unfold_locales)(auto dest: red_new_thread_heap)

interpretation red_mthr: multithreaded "final_expr" "mred P"
by(rule red_mthr)

lemmas red_mthr_redT_elims4 = red_mthr.redT_elims4[consumes 1, case_names normal acquire]

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
by(erule red_mthr.redT.cases, auto dest: red_hext_incr)

text {* Towards agreement between the framework semantics' lock state and the locks stored in the expressions *}

consts
  sync_ok :: "('a,'b) exp \<Rightarrow> bool"
  sync_oks :: "('a,'b) exp list \<Rightarrow> bool"

primrec
  "sync_ok (new C) = True"
  "sync_ok (newA T\<lfloor>i\<rceil>) = sync_ok i"
  "sync_ok (Cast T e) = sync_ok e"
  "sync_ok (Val v) = True"
  "sync_ok (Var v) = True"
  "sync_ok (e \<guillemotleft>bop\<guillemotright> e') = (sync_ok e \<and> sync_ok e' \<and> (contains_insync e' \<longrightarrow> is_val e))"
  "sync_ok (V := e) = sync_ok e"
  "sync_ok (a\<lfloor>i\<rceil>) = (sync_ok a \<and> sync_ok i \<and> (contains_insync i \<longrightarrow> is_val a))"
  "sync_ok (AAss a i e) = (sync_ok a \<and> sync_ok i \<and> sync_ok e \<and> (contains_insync i \<longrightarrow> is_val a) \<and> (contains_insync e \<longrightarrow> is_val a \<and> is_val i))"
  "sync_ok (a\<bullet>length) = sync_ok a"
  "sync_ok (e\<bullet>F{D}) = sync_ok e"
  "sync_ok (FAss e F D e') = (sync_ok e \<and> sync_ok e' \<and> (contains_insync e' \<longrightarrow> is_val e))"
  "sync_ok (e\<bullet>m(pns)) = (sync_ok e \<and> sync_oks pns \<and> (contains_insyncs pns \<longrightarrow> is_val e))"
  "sync_ok ({V : T=vo; e}\<^bsub>cr\<^esub>) = sync_ok e"
  "sync_ok (sync\<^bsub>V\<^esub> (o') e) = (sync_ok o' \<and> \<not> contains_insync e)"
  "sync_ok (insync\<^bsub>V\<^esub> (a) e) = sync_ok e"
  "sync_ok (e;;e') = (sync_ok e \<and> sync_ok e' \<and> (contains_insync e' \<longrightarrow> is_val e))"
  "sync_ok (if (b) e else e') = (sync_ok b \<and> \<not> contains_insync e \<and> \<not> contains_insync e')"
  "sync_ok (while (b) e) = (\<not> contains_insync b \<and> \<not> contains_insync e)"
  "sync_ok (throw e) = sync_ok e"
  "sync_ok (try e catch(C v) e') = (sync_ok e \<and> \<not> contains_insync e')"
  "sync_oks [] = True"
  "sync_oks (x # xs) = (sync_ok x \<and> sync_oks xs \<and> (contains_insyncs xs \<longrightarrow> is_val x))"

lemma sync_oks_append [simp]:
  "sync_oks (xs @ ys) \<longleftrightarrow> sync_oks xs \<and> sync_oks ys \<and> (contains_insyncs ys \<longrightarrow> (\<exists>vs. xs = map Val vs))"
by(induct xs)(auto simp add: Cons_eq_map_conv)

lemma fixes e :: "('a,'b) exp" and es :: "('a,'b) exp list"
  shows not_contains_insync_sync_ok: "\<not> contains_insync e \<Longrightarrow> sync_ok e"
  and not_contains_insyncs_sync_oks: "\<not> contains_insyncs es \<Longrightarrow> sync_oks es"
by(induct e and es)(auto)

lemma expr_locks_sync_ok: "(\<And>ad. expr_locks e ad = 0) \<Longrightarrow> sync_ok e"
  and expr_lockss_sync_oks: "(\<And>ad. expr_lockss es ad = 0) \<Longrightarrow> sync_oks es"
by(auto intro!: not_contains_insync_sync_ok not_contains_insyncs_sync_oks
        simp add: contains_insync_conv contains_insyncs_conv)

lemma sync_ok_extRet2J [simp]: "sync_ok (extRet2J va)"
by(cases va) auto

lemma 
  assumes wf: "wf_J_prog P"
  shows red_preserve_sync_ok: "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> sync_ok e'"
  and reds_preserve_sync_oks: "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk> \<Longrightarrow> sync_oks es'"
proof(induct rule: red_reds.inducts)
  case (RedCall s a C fs M vs Ts T pns body D)
  from wf `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
  have "wf_mdecl wf_J_mdecl P D (M,Ts,T,pns,body)"
    by(rule sees_wf_mdecl)
  then obtain T where "P,[this\<mapsto>Class D,pns[\<mapsto>]Ts] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
  with `length vs = length pns` `length Ts = length pns` 
  have "expr_locks (blocks (pns, Ts, vs, body)) = (\<lambda>ad. 0)"
    by(simp add: expr_locks_blocks)
  thus ?case by(auto intro: expr_locks_sync_ok)
qed(fastsimp intro: not_contains_insync_sync_ok)+

lemma assumes wf: "wf_J_prog P"
  shows expr_locks_new_thread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t (e'', x'') h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> expr_locks e'' = (\<lambda>ad. 0)"

  and expr_locks_new_thread':
  "\<lbrakk> P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t (e'', x'') h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> expr_locks e'' = (\<lambda>ad. 0)"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  then obtain C fs where subThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" and ext: "extNTA2J P (C, run, t) = (e'', x'')"
    by(fastsimp elim!: red_external.cases split: heapobj.split_asm dest: Array_widen)
  from sub_Thread_sees_run[OF wf subThread] obtain D pns body
    where sees: "P \<turnstile> C sees run: []\<rightarrow>Void = (pns, body) in D" by auto
  from sees_wf_mdecl[OF wf this] obtain T where "P,[this \<mapsto> Class D] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
  with sees ext show ?case by(auto simp add: extNTA2J_def)
qed(auto)

lemma assumes wf: "wf_J_prog P"
  shows red_new_thread_sync_ok: "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> sync_ok e''"
  and reds_new_thread_sync_ok: "\<lbrakk> P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> sync_ok e''"
by(auto dest!: expr_locks_new_thread[OF wf] expr_locks_new_thread'[OF wf] intro: expr_locks_sync_ok expr_lockss_sync_oks)

abbreviation
  sync_es_ok :: "(addr,thread_id,('a,'b) exp\<times>'c) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "sync_es_ok \<equiv> ts_ok (\<lambda>(e, x) m. sync_ok e)"

lemma lifting_wf_sync_ok: "wf_J_prog P \<Longrightarrow> lifting_wf (mred P) (\<lambda>(e, x) m. sync_ok e)"
by(unfold_locales)(auto intro: red_preserve_sync_ok red_new_thread_sync_ok)

lemma redT_preserve_sync_ok:
  assumes red: "P \<turnstile> s -t\<triangleright>ta\<rightarrow> s'"
  shows "\<lbrakk> wf_J_prog P; sync_es_ok (thr s) (shr s) \<rbrakk> \<Longrightarrow> sync_es_ok (thr s') (shr s')"
by(rule lifting_wf.redT_preserves[OF lifting_wf_sync_ok red])

lemmas RedT_preserves_sync_ok = lifting_wf.RedT_preserves[OF lifting_wf_sync_ok]

text {* Framework lock state agrees with locks stored in the expression *}

definition lock_ok :: "(addr,thread_id) locks \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<Rightarrow> bool" where
  "lock_ok ls ts \<equiv> \<forall>t. (case (ts t) of None    \<Rightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t = 0)
                                     | \<lfloor>((e, x), ln)\<rfloor> \<Rightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_locks e l))"

lemma lock_okI:
  "\<lbrakk> \<And>t l. ts t = None \<Longrightarrow> has_locks (ls\<^sub>f l) t = 0; \<And>t e x ln l. ts t = \<lfloor>((e, x), ln)\<rfloor> \<Longrightarrow> has_locks (ls\<^sub>f l) t + ln\<^sub>f l= expr_locks e l \<rbrakk> \<Longrightarrow> lock_ok ls ts"
apply(fastsimp simp add: lock_ok_def)
done

lemma lock_okE:
  "\<lbrakk> lock_ok ls ts;
     \<forall>t. ts t = None \<longrightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t = 0) \<Longrightarrow> Q;
     \<forall>t e x ln. ts t = \<lfloor>((e, x), ln)\<rfloor> \<longrightarrow> (\<forall>l. has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_locks e l) \<Longrightarrow> Q \<rbrakk>
  \<Longrightarrow> Q"
by(fastsimp simp add: lock_ok_def)

lemma lock_okD1:
  "\<lbrakk> lock_ok ls ts; ts t = None \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls\<^sub>f l) t = 0"
apply(simp add: lock_ok_def)
apply(erule_tac x="t" in allE)
apply(auto)
done

lemma lock_okD2:
  "\<lbrakk> lock_ok ls ts; ts t = \<lfloor>((e, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_locks e l"
apply(fastsimp simp add: lock_ok_def)
done

lemma lock_ok_lock_thread_ok:
  assumes lock: "lock_ok ls ts"
  shows "lock_thread_ok ls ts"
proof(rule lock_thread_okI)
  fix l t
  assume lsl: "has_lock (ls\<^sub>f l) t"
  show "\<exists>xw. ts t = \<lfloor>xw\<rfloor>"
  proof(cases "ts t")
    case None
    with lock have "has_locks (ls\<^sub>f l) t = 0"
      by(auto dest: lock_okD1)
    with lsl show ?thesis by simp
  next
    case (Some a) thus ?thesis by blast
  qed
qed

text {* Preservation of lock state agreement *}

fun upd_expr_lock_action :: "int \<Rightarrow> lock_action \<Rightarrow> int"
where
  "upd_expr_lock_action i Lock = i + 1"
| "upd_expr_lock_action i Unlock = i - 1"
| "upd_expr_lock_action i UnlockFail = i"
| "upd_expr_lock_action i ReleaseAcquire = i"

fun upd_expr_lock_actions :: "int \<Rightarrow> lock_action list \<Rightarrow> int" where
  "upd_expr_lock_actions n [] = n"
| "upd_expr_lock_actions n (L # Ls) = upd_expr_lock_actions (upd_expr_lock_action n L) Ls"

lemma upd_expr_lock_actions_append [simp]:
  "upd_expr_lock_actions n (Ls @ Ls') = upd_expr_lock_actions (upd_expr_lock_actions n Ls) Ls'"
by(induct Ls arbitrary: n, auto)

definition upd_expr_locks :: "('l \<Rightarrow> int) \<Rightarrow> 'l lock_actions \<Rightarrow> 'l \<Rightarrow> int"
where "upd_expr_locks els las \<equiv> \<lambda>l. upd_expr_lock_actions (els l) (las\<^sub>f l)"

lemma upd_expr_locks_iff [simp]:
  "upd_expr_locks els las l = upd_expr_lock_actions (els l) (las\<^sub>f l)"
by(simp add: upd_expr_locks_def)

lemma upd_expr_lock_action_add [simp]:
  "upd_expr_lock_action (l + l') L = upd_expr_lock_action l L + l'"
by(cases L, auto)

lemma upd_expr_lock_actions_add [simp]:
  "upd_expr_lock_actions (l + l') Ls = upd_expr_lock_actions l Ls + l'"
by(induct Ls arbitrary: l, auto)

lemma upd_expr_locks_add [simp]:
  "upd_expr_locks (\<lambda>a. x a + y a) las = (\<lambda>a. upd_expr_locks x las a + y a)"
by(auto intro: ext)

lemma expr_locks_extRet2J [simp]: "expr_locks (extRet2J va) = (\<lambda>ad. 0)"
by(cases va) auto

lemma assumes wf: "wf_J_prog P"
  shows red_update_expr_locks:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"
  and reds_update_expr_lockss:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk> \<Longrightarrow> upd_expr_locks (int o expr_lockss es) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_lockss es'"
proof -
  have "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_locks e') ad - (int o expr_locks e) ad)"
    and "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk> \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_lockss es') ad - (int o expr_lockss es) ad)"
  proof(induct rule: red_reds.inducts)
    case (RedCall s a C fs M vs Ts T pns body D)
    from wf `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
    have "wf_mdecl wf_J_mdecl P D (M,Ts,T,pns,body)"
      by(rule sees_wf_mdecl)
    then obtain T where "P,[this\<mapsto>Class D,pns[\<mapsto>]Ts] \<turnstile> body :: T"
      by(auto simp add: wf_mdecl_def)
    hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
    with `length vs = length pns` `length Ts = length pns` 
    have "expr_locks (blocks (pns, Ts, vs, body)) = (\<lambda>ad. 0)"
      by(simp add: expr_locks_blocks)
    thus ?case by(auto intro: expr_locks_sync_ok)
  next
    case RedCallExternal thus ?case
      by(auto simp add: expand_fun_eq contains_insync_conv contains_insyncs_conv finfun_upd_apply elim!: red_external.cases)
  qed(fastsimp simp add: expand_fun_eq contains_insync_conv contains_insyncs_conv finfun_upd_apply)+
  hence "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_locks e) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'"
    and "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk> \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_lockss es) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_lockss es'"
    by(auto intro: ext simp only: upd_expr_locks_add)
  thus "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"
    and "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk> \<Longrightarrow> upd_expr_locks (int o expr_lockss es) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_lockss es'"
    by(auto simp add: o_def)
qed

definition lock_expr_locks_ok :: "'t FWState.lock \<Rightarrow> 't \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "lock_expr_locks_ok l t n i \<equiv> (i = int (has_locks l t) + int n) \<and> i \<ge> 0"

lemma upd_lock_upd_expr_lock_action_preserve_lock_expr_locks_ok:
  assumes lao: "lock_action_ok l t L"
  and lelo: "lock_expr_locks_ok l t n i"
  shows "lock_expr_locks_ok (upd_lock l t L) t (upd_threadR n l t L) (upd_expr_lock_action i L)"
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
  \<Longrightarrow> lock_expr_locks_ok (upd_locks l t Ls) t (upd_threadRs n l t Ls) (upd_expr_lock_actions i Ls)"
by(induct Ls arbitrary: l i n)(auto intro: upd_lock_upd_expr_lock_action_preserve_lock_expr_locks_ok)


definition ls_els_ok :: "(addr,thread_id) locks \<Rightarrow> thread_id \<Rightarrow> (addr \<Rightarrow>\<^isub>f nat) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> bool" where
  "ls_els_ok ls t ln els \<equiv> \<forall>l. lock_expr_locks_ok (ls\<^sub>f l) t (ln\<^sub>f l) (els l)"

lemma ls_els_okI:
  "(\<And>l. lock_expr_locks_ok (ls\<^sub>f l) t (ln\<^sub>f l) (els l)) \<Longrightarrow> ls_els_ok ls t ln els"
by(auto simp add: ls_els_ok_def)

lemma ls_els_okE:
  "\<lbrakk> ls_els_ok ls t ln els; \<forall>l. lock_expr_locks_ok (ls\<^sub>f l) t (ln\<^sub>f l) (els l) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: ls_els_ok_def)

lemma ls_els_okD:
  "ls_els_ok ls t ln els \<Longrightarrow> lock_expr_locks_ok (ls\<^sub>f l) t (ln\<^sub>f l) (els l)"
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
      and cctta: "thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
      and ls': "ls' = redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
      and es': "ts' = redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> ((e', x'), redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))"
      and ws': "ws' = redT_updWs ws t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
      by auto
    from est aoes have aoe: "sync_ok e" by(auto dest: ts_okD)
    from aoe P have aoe': "sync_ok e'" by(auto dest: red_preserve_sync_ok[OF wf])
    from aoes red_new_thread_sync_ok[OF wf P]
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
      with loes have "has_locks (ls\<^sub>f l) t'' = 0"
	by(auto dest: lock_okD1)
      moreover from `ts' t'' = None` es'
      have "t \<noteq> t''" by(simp split: split_if_asm)
      ultimately show "has_locks (ls'\<^sub>f l) t'' = 0"
	by(simp add: red_mthr.redT_has_locks_inv[OF redT])
    next
      fix t'' e'' x'' l ln''
      assume ts't'': "ts' t'' = \<lfloor>((e'', x''), ln'')\<rfloor>"
      with aoes' es' have aoe'': "sync_ok e''" by(auto dest: ts_okD)
      show "has_locks (ls'\<^sub>f l) t'' + ln''\<^sub>f l = expr_locks e'' l"
      proof(cases "t = t''")
	case True
	note tt'' = `t = t''`
	with ts't'' es' have  e'': "e'' = e'" and x'': "x'' = x'"
	  and ln'': "ln'' = redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
	have "ls_els_ok ls t no_wait_locks (int o expr_locks e)"
	proof(rule ls_els_okI)
	  fix l
	  note lock_okD2[OF loes, OF est]
	  thus "lock_expr_locks_ok (ls\<^sub>f l) t (no_wait_locks\<^sub>f l) ((int \<circ> expr_locks e) l)"
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
	from lota have lao: "lock_actions_ok (ls\<^sub>f l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)"
	  by(simp add: lock_ok_las_def)
	show ?thesis
	proof(cases "ts t''")
	  case None
	  with est ts't'' es' tt'' cctta
	  obtain m' where "NewThread t'' (e'', x'') m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" and ln'': "ln'' = no_wait_locks"
	    by(auto dest: redT_updTs_new_thread)
	  moreover with P have "m' = h'" by(auto dest: red_new_thread_heap)
	  ultimately have "NewThread t'' (e'', x'') h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by simp
	  with wf P ln'' have "expr_locks e'' = (\<lambda>ad. 0)"
	    by -(rule expr_locks_new_thread)
	  hence elel: "expr_locks e'' l = 0" by simp
	  from loes None  have "has_locks (ls\<^sub>f l) t'' = 0"
	    by(auto dest: lock_okD1)
	  moreover note lock_actions_ok_has_locks_upd_locks_eq_has_locks[OF lao tt''[symmetric]]
	  ultimately have "has_locks ((redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<^sub>f l) t'' = 0"
	    by(auto simp add: expand_fun_eq)
	  with elel ls' ln'' show ?thesis by(auto)
	next
	  case (Some a)
	  then obtain E X LN where est'': "ts t'' = \<lfloor>((E, X), LN)\<rfloor>" by(cases a, auto)
	  with loes have IH: "has_locks (ls\<^sub>f l) t'' + LN\<^sub>f l = expr_locks E l"
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
      from tst'' loes have "has_locks (ls\<^sub>f l) t'' = 0"
	by(auto dest: lock_okD1)
      thus "has_locks (ls'\<^sub>f l) t'' = 0"
	by(simp add: red_mthr.redT_has_locks_inv[OF redT tt''])
    next
      fix t'' e'' x'' ln'' l
      assume ts't'': "ts' t'' = \<lfloor>((e'', x''), ln'')\<rfloor>"
      show "has_locks (ls'\<^sub>f l) t'' + ln''\<^sub>f l = expr_locks e'' l"
      proof(cases "t = t''")
	case True
	note [simp] = this
	with ts't'' ts' tst
	have [simp]: "ln'' = no_wait_locks" "e = e''" by auto
	from tst loes have "has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_locks e l"
	  by(auto dest: lock_okD2)
	show ?thesis
	proof(cases "ln\<^sub>f l > 0")
	  case True
	  with `may_acquire_all ls t ln` ls' have "may_lock (ls\<^sub>f l) t"
	    by(auto elim: may_acquire_allE)
	  with ls'
	  have "has_locks (ls'\<^sub>f l) t = has_locks (ls\<^sub>f l) t + ln\<^sub>f l"
	    by(simp add: has_locks_acquire_locks_conv)
	  with `has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_locks e l`
	  show ?thesis by(simp)
	next
	  case False
	  hence "ln\<^sub>f l = 0" by simp
	  with ls' have "has_locks (ls'\<^sub>f l) t = has_locks (ls\<^sub>f l) t"
	    by(simp)
	  with `has_locks (ls\<^sub>f l) t + ln\<^sub>f l = expr_locks e l` `ln\<^sub>f l = 0`
	  show ?thesis by(simp)
	qed
      next
	case False
	with ts' ts't'' have tst'': "ts t'' = \<lfloor>((e'', x''), ln'')\<rfloor>" by(simp)
	with loes have "has_locks (ls\<^sub>f l) t'' + ln''\<^sub>f l = expr_locks e'' l"
	  by(auto dest: lock_okD2)
	show ?thesis
	proof(cases "ln\<^sub>f l > 0")
	  case False
	  with `t \<noteq> t''` ls'
	  have "has_locks (ls'\<^sub>f l) t'' = has_locks (ls\<^sub>f l) t''" by(simp)
	  with `has_locks (ls\<^sub>f l) t'' + ln''\<^sub>f l = expr_locks e'' l`
	  show ?thesis by(simp)
	next
	  case True
	  with `may_acquire_all ls t ln` have "may_lock (ls\<^sub>f l) t"
	    by(auto elim: may_acquire_allE)
	  with ls' `t \<noteq> t''` have "has_locks (ls'\<^sub>f l) t'' = has_locks (ls\<^sub>f l) t''"
	    by(simp add: has_locks_acquire_locks_conv')
	  with ls' `has_locks (ls\<^sub>f l) t'' + ln''\<^sub>f l = expr_locks e'' l`
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
proof(induct rule: red_mthr.RedT_induct[consumes 1, case_names refl step])
  case refl thus ?case by blast
next
  case step thus ?case
    apply -
    apply(erule redT_preserves_lock_ok[OF wf], assumption)
    by(auto dest: RedT_preserves_sync_ok[OF wf])
qed

lemma red_NewThread_Thread_Object:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>C fs. hp s' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
  and reds_NewThread_Thread_Object:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>C fs. hp s' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(induct rule: red_reds.inducts)
apply(fastsimp dest: red_external_new_thread_exists_thread_object)+
done

lemma redT_NewThread_Thread_Object:
  "\<lbrakk> P \<turnstile> s -t'\<triangleright>ta\<rightarrow> s'; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>C fs. shr s' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
by(auto elim!: red_mthr.redT.cases dest:red_NewThread_Thread_Object)

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
      and [simp]: "ln = no_wait_locks" by(auto dest: red_mthr.redT_new_thread)
    from red nt obtain C fs where "shr s' t = \<lfloor>Obj C fs\<rfloor>" "P \<turnstile> Class C \<le> Class Thread"
      by(auto dest!: redT_NewThread_Thread_Object)
    thus ?thesis by(clarsimp)
  next
    case (Some Xln)
    with tc obtain T where "typeof\<^bsub>shr s\<^esub> (Addr t) = \<lfloor>T\<rfloor>" "P \<turnstile> T \<le> Class Thread"
      by(rule thread_confDE)
    moreover from red have "hext (shr s) (shr s')"
      by(cases s, cases s')(auto intro: redT_hext_incr)
    ultimately have "typeof\<^bsub>shr s'\<^esub> (Addr t) = \<lfloor>T\<rfloor>"
      by(blast dest: type_of_hext_type_of hext_objarrD)
    with `P \<turnstile> T \<le> Class Thread` show ?thesis by blast
  qed
qed
    
lemma RedT_preserves_thread_conf:
  "\<lbrakk> P \<turnstile> s -\<triangleright>tta\<rightarrow>* s'; thread_conf P (thr s) (shr s) \<rbrakk> \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(rule red_mthr.RedT_lift_preserveD[OF _ _ redT_preserves_thread_conf])

end
