(*  Title:      JinjaThreads/J/ProgressThreaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Progress and type safety theorem for the multithreaded system} *}

theory ProgressThreaded 
imports Threaded TypeSafe "../Framework/FWProgress"
begin

text {* translating syntax *}

syntax
  can_sync_syntax :: "J_prog \<Rightarrow> expr \<Rightarrow> heap \<times> locals \<Rightarrow> addr set \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>" [50,0,0,0] 81)

translations
  "P \<turnstile> \<langle>e, s\<rangle> L \<wrong>" => "multithreaded_base.can_sync ((CONST mred) P) (e, snd s) (fst s) L"
  "P \<turnstile> \<langle>e, (h, x)\<rangle> L \<wrong>" == "multithreaded_base.can_sync ((CONST mred) P) (e, x) h L"

syntax
  must_sync_syntax :: "J_prog \<Rightarrow> expr \<Rightarrow> heap \<times> locals \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>" [50,0,0] 81)

translations
  "P \<turnstile> \<langle>e, s\<rangle> \<wrong>" => "multithreaded_base.must_sync ((CONST mred) P) (e, snd s) (fst s)"
  "P \<turnstile> \<langle>e, (h, x)\<rangle> \<wrong>" == "multithreaded_base.must_sync ((CONST mred) P) (e, x) h"


lemma lock_ok_ls_Some_ex_ts_not_final:
  assumes lock: "lock_ok ls ts"
  and hl: "has_lock (ls\<^sub>f l) t"
  shows "\<exists>e x ln. ts t = \<lfloor>((e, x), ln)\<rfloor> \<and> \<not> final e"
proof -
  from lock have "lock_thread_ok ls ts"
    by(rule lock_ok_lock_thread_ok)
  with hl obtain e x ln
    where tst: "ts t = \<lfloor>((e, x), ln)\<rfloor>"
    by(auto dest!: lock_thread_okD)
  { assume "final e"
    hence "expr_locks e l = 0" by(rule final_locks)
    with lock tst have "has_locks (ls\<^sub>f l) t = 0"
      by(auto dest: lock_okD2[rule_format, where l=l])
    with hl have False by simp }
  with tst show ?thesis by auto
qed


section {* Preservation lemmata *}

text {* Definite assignment *}

abbreviation
  def_ass_ts_ok :: "(addr,thread_id,expr \<times> locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "def_ass_ts_ok \<equiv> ts_ok (\<lambda>(e, x) h. \<D> e \<lfloor>dom x\<rfloor>)"

lemma assumes wf: "wf_J_prog P"
  shows red_def_ass_new_thread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') c'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<D> e'' \<lfloor>dom x''\<rfloor>"
  
  and reds_def_ass_new_thread:
  "\<lbrakk> P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') c'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<D> e'' \<lfloor>dom x''\<rfloor>"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  then obtain C fs where subThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" and ext: "extNTA2J P (C, run, t'') = (e'', x'')"
    by(fastsimp elim!: red_external.cases split: heapobj.split_asm dest: Array_widen)
  from sub_Thread_sees_run[OF wf subThread] obtain D pns body
    where sees: "P \<turnstile> C sees run: []\<rightarrow>Void = (pns, body) in D" by auto
  from sees_wf_mdecl[OF wf this] have "\<D> body \<lfloor>{this}\<rfloor>"
    by(auto simp add: wf_mdecl_def)
  with sees ext show ?case by(clarsimp simp del: fun_upd_apply)
qed(auto)

lemma lifting_wf_def_ass: "wf_J_prog P \<Longrightarrow> lifting_wf (mred P) (\<lambda>(e, x) m. \<D> e \<lfloor>dom x\<rfloor>)"
apply(unfold_locales)
apply(auto dest: red_preserves_defass red_def_ass_new_thread)
done

lemmas redT_preserves_defass = lifting_wf.redT_preserves[OF lifting_wf_def_ass]
lemmas RedT_preserves_defass = lifting_wf.RedT_preserves[OF lifting_wf_def_ass]

text {* typeability *}

constdefs
  type_ok :: "J_prog \<Rightarrow> env \<times> ty \<Rightarrow> expr \<Rightarrow> heap \<Rightarrow> bool"
  "type_ok P \<equiv> (\<lambda>(E, T) e c. (\<exists>T'. (P,E,c \<turnstile> e : T' \<and> P \<turnstile> T' \<le> T)))"

lemma red_preserves_type_ok: 
  "\<lbrakk> extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; wf_J_prog P; P,E \<turnstile> s \<surd>; type_ok P (E, T) e (hp s) \<rbrakk> \<Longrightarrow> type_ok P (E, T) e' (hp s')"
apply(clarsimp simp add: type_ok_def)
apply(subgoal_tac "\<exists>T''. P,E,hp s' \<turnstile> e' : T'' \<and> P \<turnstile> T'' \<le> T'")
 apply(fast elim: widen_trans)
by(rule subject_reduction)

lemma red_preserve_welltype:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; P,E,h \<turnstile> e'' : T \<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e'' : T"
by(auto elim: WTrt_hext_mono dest!: red_hext_incr)

definition sconf_type_ok :: "J_prog \<Rightarrow> (env \<times> ty) \<Rightarrow> expr \<Rightarrow> heap \<Rightarrow> locals \<Rightarrow> bool" where
  "sconf_type_ok P ET e h l \<equiv> P,fst ET \<turnstile> (h, l) \<surd> \<and> type_ok P ET e h"

abbreviation
  sconf_type_ts_ok :: "J_prog \<Rightarrow> (thread_id \<rightharpoonup> (env \<times> ty)) \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "sconf_type_ts_ok \<equiv> \<lambda>P. ts_inv (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x)"

lemma fixes E :: env
  assumes wf: "wf_J_prog P"
  shows red_type_newthread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>E T. P,E,hp s' \<turnstile> e'' : T \<and> P,hp s' \<turnstile> x'' (:\<le>) E"
  and reds_type_newthread:
  "\<lbrakk> P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; P,E,hp s \<turnstile> es [:] Ts \<rbrakk>
  \<Longrightarrow> \<exists>E T. P,E,hp s' \<turnstile> e'' : T \<and> P,hp s' \<turnstile> x'' (:\<le>) E"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedCallExternal s a U M vs ta va h' ta' e' s')
  from `NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>` `ta' = extTA2J P ta`
  obtain C' M' a' where nt: "NewThread t'' (C', M', a') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
    and "extNTA2J P (C', M', a') = (e'', x'')" by fastsimp
  from red_external_new_thread_sees[OF wf `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` nt] `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>U\<rfloor>`
  obtain fs T pns body D where h'a': "h' a' = \<lfloor>Obj C' fs\<rfloor>"
    and sees: " P \<turnstile> C' sees M': []\<rightarrow>T = (pns, body) in D" by auto
  from sees_wf_mdecl[OF wf sees] obtain T where "P,[this \<mapsto> Class D] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "WTrt P (hp s') [this \<mapsto> Class D] body T" by(rule WT_implies_WTrt)
  moreover from sees have "P \<turnstile> C' \<preceq>\<^sup>* D" by(rule sees_method_decl_above)
  with h'a' have "P,h' \<turnstile> [this \<mapsto> Addr a'] (:\<le>) [this \<mapsto> Class D]" by(auto simp add: lconf_def conf_def)
  ultimately show ?case using h'a' sees `s' = (h', lcl s)`
    `extNTA2J P (C', M', a') = (e'', x'')` by(fastsimp intro: sees_method_decl_above)
qed(fastsimp)+

lemma lifting_inv_sconf_subject_ok:
  assumes wf: "wf_J_prog P"
  shows "lifting_inv (mred P) (\<lambda>x m. True) (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x)"
proof(rule lifting_inv.intro[OF _ lifting_inv_axioms.intro])
  show "lifting_wf (mred P) (\<lambda>x m. True)" by(unfold_locales)
next
  fix x m ta x' m' i
  assume "mred P (x, m) ta (x', m')"
    and "(\<lambda>(e, x) m. sconf_type_ok P i e m x) x m"
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  ultimately have sconf_type: "sconf_type_ok P (E, T) e m l"
    and red: "P \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>" by auto
  from sconf_type have sconf: "P,E \<turnstile> (m, l) \<surd>" and "type_ok P (E, T) e m"
    by(auto simp add: sconf_type_ok_def)
  then obtain T' where "P,E,m \<turnstile> e : T'" "P \<turnstile> T' \<le> T" by(auto simp add: type_ok_def)
  from `P,E \<turnstile> (m, l) \<surd>` `P,E,m \<turnstile> e : T'` red
  have "P,E \<turnstile> (m', l') \<surd>" by(auto elim: red_preserves_sconf)
  moreover
  from red `P,E,m \<turnstile> e : T'` wf `P,E \<turnstile> (m, l) \<surd>`
  obtain T'' where "P,E,m' \<turnstile> e' : T''" "P \<turnstile> T'' \<le> T'"
    by(auto dest: subject_reduction)
  note `P,E,m' \<turnstile> e' : T''`
  moreover
  from `P \<turnstile> T'' \<le> T'` `P \<turnstile> T' \<le> T`
  have "P \<turnstile> T'' \<le> T" by(rule widen_trans)
  ultimately have "sconf_type_ok P (E, T) e' m' l'"
    by(auto simp add: sconf_type_ok_def type_ok_def)
  thus "(\<lambda>(e, x) m. sconf_type_ok P i e m x) x' m'" by simp
next
  fix x m ta x' m' i t'' x''
  assume "mred P (x, m) ta (x', m')"
    and "(\<lambda>(e, x) m. sconf_type_ok P i e m x) x m"
    and "NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  moreover obtain e'' l'' where x'' [simp]: "x'' = (e'', l'')" by(cases x'', auto) 
  ultimately have sconf_type: "sconf_type_ok P (E, T) e m l"
    and red: "P \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>"
    and nt: "NewThread t'' (e'', l'') m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by auto
  from sconf_type have sconf: "P,E \<turnstile> (m, l) \<surd>" and "type_ok P (E, T) e m"
    by(auto simp add: sconf_type_ok_def)
  then obtain T' where "P,E,m \<turnstile> e : T'" "P \<turnstile> T' \<le> T" by(auto simp add: type_ok_def)
  from nt `P,E,m \<turnstile> e : T'` red have "\<exists>E T. P,E,m' \<turnstile> e'' : T \<and> P,m' \<turnstile> l'' (:\<le>) E"
    by(fastsimp dest: red_type_newthread[OF wf])
  then obtain E'' T'' where "P,E'',m' \<turnstile> e'' : T''" "P,m' \<turnstile> l'' (:\<le>) E''" by blast
  moreover
  from sconf red `P,E,m \<turnstile> e : T'` have "P,E \<turnstile> (m', l') \<surd>"
    by(auto intro: red_preserves_sconf)
  hence "P \<turnstile> m' \<surd>" by(auto simp add: sconf_def)
  ultimately show "\<exists>i''. (\<lambda>(e, x) m. sconf_type_ok P i'' e m x) x'' m'"
    by(auto simp add: sconf_type_ok_def type_ok_def sconf_def intro: widen_refl)
next
  fix x m ta x' m' i i'' x''
  assume "mred P (x, m) ta (x', m')" 
    and "(\<lambda>(e, x) m. sconf_type_ok P i e m x) x m"
    and "(\<lambda>(e, x) m. sconf_type_ok P i'' e m x) x'' m"
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  moreover obtain e'' l'' where x'' [simp]: "x'' = (e'', l'')" by(cases x'', auto)
  moreover obtain E'' T'' where i'' [simp]: "i'' = (E'', T'')" by(cases i'', auto)
  ultimately have sconf_type: "sconf_type_ok P (E, T) e m l"
    and red: "P \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>"
    and sc: "sconf_type_ok P (E'', T'') e'' m l''" by auto
  from sconf_type obtain T' where "P,E,m \<turnstile> e : T'" by(auto simp add: sconf_type_ok_def type_ok_def)
  from sc have sconf: "P,E'' \<turnstile> (m, l'') \<surd>" and "type_ok P (E'', T'') e'' m"
    by(auto simp add: sconf_type_ok_def)
  then obtain T''' where "P,E'',m \<turnstile> e'' : T'''" "P \<turnstile> T''' \<le> T''" by(auto simp add: type_ok_def)
  moreover from red `P,E'',m \<turnstile> e'' : T'''` have "P,E'',m' \<turnstile> e'' : T'''"
    by(rule red_preserve_welltype)
  moreover from sconf have "P \<turnstile> m \<surd>" by(simp add: sconf_def)
  with red `P,E,m \<turnstile> e : T'` have "P \<turnstile> m' \<surd>"
    by(auto dest: red_preserves_hconf)
  moreover {
    from red have "hext m m'" by(auto dest: red_hext_incr)
    moreover from sconf have "P,m \<turnstile> l'' (:\<le>) E''"
      by(simp add: sconf_def)
    ultimately have "P,m' \<turnstile> l'' (:\<le>) E''" by-(rule lconf_hext) }
  ultimately have "sconf_type_ok P (E'', T'') e'' m' l''"
    by(auto simp add: sconf_type_ok_def sconf_def type_ok_def)
  thus "(\<lambda>(e, x) m. sconf_type_ok P i'' e m x) x'' m'" by simp
qed

lemmas redT_invariant_sconf_type = lifting_inv.redT_invariant[OF lifting_inv_sconf_subject_ok]

lemmas RedT_invariant_sconf_type = lifting_inv.RedT_invariant[OF lifting_inv_sconf_subject_ok]

lemmas RedT_preserves_es_inv_ok = red_mthr.RedT_preserves_ts_inv_ok

text {* wf\_red *}

lemma red_wf_red_aux:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; \<not> final_thread.actions_ok' (ls, (ts, m), ws) t ta; sync_ok e;
     \<forall>l. has_locks (ls\<^sub>f l) t \<ge> expr_locks e l \<rbrakk>
    \<Longrightarrow> \<exists>e'' s'' ta'. P \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e'',s''\<rangle> \<and> red_mthr.actions_ok' (ls, (ts, m), ws) t ta' \<and> red_mthr.actions_subset ta' ta"
  (is "\<lbrakk> _; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e s ta")
and
  "\<lbrakk> P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; \<not> final_thread.actions_ok' (ls, (ts, m), ws) t ta; sync_oks es;
     \<forall>l. has_locks (ls\<^sub>f l) t \<ge> expr_lockss es l \<rbrakk>
    \<Longrightarrow> \<exists>es'' s'' ta'. P \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es'',s''\<rangle> \<and> final_thread.actions_ok' (ls, (ts, m), ws) t ta' \<and> final_thread.actions_subset ta' ta"
proof(induct rule: red_reds.inducts)
  case (SynchronizedRed2 e s ta e' s' a)
  note IH = `\<lbrakk>\<not> final_thread.actions_ok' (ls, (ts, m), ws) t ta; sync_ok e; \<forall>l. expr_locks e l \<le> has_locks (ls\<^sub>f l) t\<rbrakk>
            \<Longrightarrow> ?concl e s ta`
  note `\<not> final_thread.actions_ok' (ls, (ts, m), ws) t ta`
  moreover from `sync_ok (insync(a) e)` have "sync_ok e" by simp
  moreover from `\<forall>l. expr_locks (insync(a) e) l \<le> has_locks (ls\<^sub>f l) t`
  have "\<forall>l. expr_locks e l \<le> has_locks (ls\<^sub>f l) t" by(force split: split_if_asm)
  ultimately have "?concl e s ta" by(rule IH)
  thus ?case by(fastsimp intro: red_reds.SynchronizedRed2)
next
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  from `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>`
  obtain ta'' va' h'' where red': "P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta''\<rightarrow>ext \<langle>va',h''\<rangle>"
    and aoe': "final_thread.actions_ok' (ls, (ts, m), ws) t ta''"
    and sub: "final_thread.actions_subset ta'' ta" by(rule red_external_wf_red)
  from aoe' have "red_mthr.actions_ok' (ls, (ts, m), ws) t (extTA2J P ta'')"
    by(simp add: final_thread.actions_ok'_convert_extTA)
  moreover from `ta' = extTA2J P ta` sub
  have "red_mthr.actions_subset (extTA2J P ta'') ta'"
    by(auto del: subsetI elim: final_thread.actions_subset.cases)
  moreover from red' `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>` `is_external_call P T M`
  obtain s'' e'' where "P \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J P ta''\<rightarrow> \<langle>e'',s''\<rangle>"
    by(fastsimp intro: red_reds.RedCallExternal)
  ultimately show ?case by blast
next
  case (LockSynchronized s a arrobj e)
  from `\<not> final_thread.actions_ok' (ls, (ts, m), ws) t \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>` have False
    by(auto simp add: lock_ok_las'_def finfun_upd_apply)
  thus ?case ..
next
  case (UnlockSynchronized a v s)
  from `\<forall>l. expr_locks (insync(a) Val v) l \<le> has_locks (ls\<^sub>f l) t`
  have "has_lock (ls\<^sub>f a) t" by(force split: split_if_asm)
  with `\<not> final_thread.actions_ok' (ls, (ts, m), ws) t \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>`
  have False by(auto simp add: lock_ok_las'_def finfun_upd_apply)
  thus ?case ..
next
  case (SynchronizedThrow2 a ad s)
  from `\<forall>l. expr_locks (insync(a) Throw ad) l \<le> has_locks (ls\<^sub>f l) t`
  have "has_lock (ls\<^sub>f a) t" by(force split: split_if_asm)
  with `\<not> final_thread.actions_ok' (ls, (ts, m), ws) t \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>`
  have False by(auto simp add: lock_ok_las'_def finfun_upd_apply)
  thus ?case ..
qed(simp_all add: is_val_iff contains_insync_expr_locks_conv contains_insyncs_expr_lockss_conv final_thread.actions_ok'_empty, (fastsimp intro: red_reds.intros)+)

lemma red_wf_red:
  assumes wf: "wf_J_prog P"
  and "sync_es_ok (thr S) (shr S)"
  and "lock_ok (locks S) (thr S)"
  shows "wf_red final_expr (mred P) S"
proof(unfold_locales)
  from `lock_ok (locks S) (thr S)`
  show "lock_thread_ok (locks S) (thr S)"
    by(rule lock_ok_lock_thread_ok)
next
  fix tta s t ex ta e'x' m'
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s"
    and "thr s t = \<lfloor>(ex, no_wait_locks)\<rfloor>"
    and "mred P (ex, shr s) ta (e'x', m')"
  moreover obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s, auto)
  moreover obtain e x where ex: "ex = (e, x)" by(cases ex, auto)
  moreover obtain e' x' where e'x': "e'x' = (e', x')" by(cases e'x', auto)
  ultimately have tst: "ts t = \<lfloor>(ex, no_wait_locks)\<rfloor>" 
    and red: "P \<turnstile> \<langle>e, (m, x)\<rangle> -ta\<rightarrow> \<langle>e', (m', x')\<rangle>" by auto
  from wf have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog)
  from `sync_es_ok (thr S) (shr S)` Red s have aeos: "sync_es_ok ts m"
    by(cases S)(auto dest: RedT_preserves_sync_ok[OF wf])
  with tst ex have aoe: "sync_ok e" by(auto dest: ts_okD)
  from `lock_ok (locks S) (thr S)` `sync_es_ok (thr S) (shr S)` Red s
  have lockok: "lock_ok ls ts" by(cases S)(auto dest: RedT_preserves_lock_ok[OF wf])

  show "\<exists>ta' x' m'. mred P (ex, shr s) ta' (x', m') \<and> red_mthr.actions_ok' s t ta' \<and> red_mthr.actions_subset ta' ta"
  proof(cases "red_mthr.actions_ok' s t ta")
    case True
    have "red_mthr.actions_subset ta ta" ..
    with True `mred P (ex, shr s) ta (e'x', m')` show ?thesis by blast
  next
    case False
    from lock_okD2[OF lockok, OF tst[unfolded ex]]
    have "\<forall>l. has_locks (ls\<^sub>f l) t \<ge> expr_locks e l" by simp
    from red_wf_red_aux[OF red False[unfolded s] aoe this] ex s show ?thesis
      by(fastsimp simp add: split_beta)
  qed
qed

lemma wf_progress: 
  assumes wf: "wf_J_prog P"
  and "sconf_type_ts_ok P Es (thr S) (shr S)"
  and "lock_thread_ok (locks S) (thr S)"
  and "def_ass_ts_ok (thr S) (shr S)"
  shows "wf_progress final_expr (mred P) S"
proof(unfold_locales)
  from `lock_thread_ok (locks S) (thr S)`
  show "lock_thread_ok (locks S) (thr S)" .
next
  fix tta s t ex ln
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s"
    and "thr s t = \<lfloor>(ex, ln)\<rfloor>"
    and "\<not> final_expr ex"
  moreover obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s, auto)
  moreover obtain e x where ex: "ex = (e, x)" by(cases ex, auto)
  ultimately have tst: "ts t = \<lfloor>(ex, ln)\<rfloor>" 
    and nfine: "\<not> final e" by auto
  from wf have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog)
  from `sconf_type_ts_ok P Es (thr S) (shr S)` Red s
  have "sconf_type_ts_ok P (upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) tta\<down>)) ts m"
    by(auto dest: RedT_invariant_sconf_type[OF wf])
  with tst ex obtain E T where "sconf_type_ok P (E, T) e m x"
    by -((drule ts_invD, assumption),(clarify,blast))
  then obtain T' where "P \<turnstile> m \<surd>" "P,E,m \<turnstile> e : T'"
    by(auto simp add: sconf_type_ok_def sconf_def type_ok_def)
  moreover
  from `def_ass_ts_ok (thr S) (shr S)` s Red have "def_ass_ts_ok ts m"
    by(cases S)(auto dest: RedT_preserves_defass[OF wf])
  with tst ex have "\<D> e \<lfloor>dom x\<rfloor>" by(auto dest: ts_okD)
  ultimately obtain e' m' x' ta' where "P \<turnstile> \<langle>e, (m, x)\<rangle> -ta'\<rightarrow> \<langle>e', (m', x')\<rangle>"
    using nfine by(auto dest: red_progress[OF wwf, where extTA="extTA2J P"])
  thus "\<exists>ta x' m'. mred P (ex, shr s) ta (x', m')" using ex s
    by(fastsimp)
qed

lemma progress_deadlock: 
  assumes wf: "wf_J_prog P"
  and "sync_es_ok (thr s) (shr s)"
  and "sconf_type_ts_ok P Es (thr s) (shr s)"
  and "def_ass_ts_ok (thr s) (shr s)"
  and "lock_ok (locks s) (thr s)"
  shows "progress final_expr (mred P) s (multithreaded_base.deadlock final_expr (mred P))"
using assms
apply -
apply(rule final_thread_wf.progress_deadlock)
  apply(rule final_thread_wf_interp)
 apply(rule wf_progress, assumption+)
  apply(rule lock_ok_lock_thread_ok, assumption+)
by(rule red_wf_red, assumption+)

lemma progress_deadlocked': 
  "\<lbrakk> wf_J_prog P; sync_es_ok (thr s) (shr s); sconf_type_ts_ok P Es (thr s) (shr s);
    def_ass_ts_ok (thr s) (shr s); lock_ok (locks s) (thr s) \<rbrakk>
  \<Longrightarrow> progress final_expr (mred P) s (multithreaded_base.deadlocked' final_expr (mred P))"
unfolding final_thread_wf.deadlock_eq_deadlocked'[symmetric, OF final_thread_wf_interp]
by(rule progress_deadlock)

lemma redT_progress_deadlocked:
  "\<lbrakk> wf_J_prog P; sync_es_ok (thr start_state) (shr start_state);
     sconf_type_ts_ok P Es (thr start_state) (shr start_state);
     def_ass_ts_ok (thr start_state) (shr start_state); lock_ok (locks start_state) (thr start_state);
     P \<turnstile> start_state -\<triangleright>ttas\<rightarrow>* s; final_thread.not_final_thread final_expr s t;
     \<not> multithreaded_base.deadlocked final_expr (mred P) s t\<rbrakk>
  \<Longrightarrow> \<exists>t' ta' s'. P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
by(rule progress.redT_progress[OF progress_deadlocked' _ _ multithreaded_base.not_deadlocked'I])

lemma redT_pregress_deadlock:
  "\<lbrakk> wf_J_prog P; sync_es_ok (thr start_state) (shr start_state);
     sconf_type_ts_ok P Es (thr start_state) (shr start_state);
     def_ass_ts_ok (thr start_state) (shr start_state); lock_ok (locks start_state) (thr start_state);
     P \<turnstile> start_state -\<triangleright>ttas\<rightarrow>* s;
     final_thread.not_final_thread final_expr s t; \<not> multithreaded_base.deadlock final_expr (mred P) s\<rbrakk>
  \<Longrightarrow> \<exists>t' ta' s'. P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
by(rule progress.redT_progress[OF progress_deadlock])

section {* Type safety proof *}

corollary TypeSafetyT:
  fixes ttas :: "(thread_id \<times> (addr,thread_id,expr \<times> locals,heap,addr,(addr,obs_event) observable) thread_action) list"
  assumes wf: "wf_J_prog P"
  and sconf_subject: "sconf_type_ts_ok P Es (thr s) (shr s)"
  and defass: "def_ass_ts_ok (thr s) (shr s)"
  and lock: "lock_ok (locks s) (thr s)"
  and addr: "sync_es_ok (thr s) (shr s)"
  and RedT: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>* s'"
  and esinv: "ts_inv_ok (thr s) Es"
  and tc: "thread_conf P (thr s) (shr s)"
  and nored: "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow> s'')"
  shows "thread_conf P (thr s') (shr s') \<and> 
         (let Es' = upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) ttas\<down>) in
          (\<forall>t e'. \<exists>x' ln'. thr s' t = \<lfloor>((e', x'), ln')\<rfloor> \<longrightarrow>
                    (\<exists>v. e' = Val v \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,shr s' \<turnstile> v :\<le> T) \<and> ln' = no_wait_locks)
                  \<or> (\<exists>a. e' = Throw a \<and> a \<in> dom (shr s') \<and> ln' = no_wait_locks)
                  \<or> multithreaded_base.deadlocked final_expr (mred P) s' t \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,shr s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)))
          \<and> Es \<unlhd> Es')"
proof(rule conjI)
  from RedT tc show "thread_conf P (thr s') (shr s')" by(rule RedT_preserves_thread_conf)
next
  let ?Es' = "upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) ttas\<down>)"
  obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by(cases s, auto)
  obtain ls' ts' m' ws' where s' [simp]: "s' = (ls', (ts', m'), ws')" by(cases s', auto)
  from wf have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog)
  from RedT defass have defass': "def_ass_ts_ok ts' m'"
    by(auto dest: RedT_preserves_defass[OF wf])
  from RedT lock addr wf have lock': "lock_ok ls' ts'"
    by (auto dest: RedT_preserves_lock_ok[OF wf])
  from RedT addr wf have addr': "sync_es_ok ts' m'"
    by(auto dest: RedT_preserves_sync_ok[OF wf])
  from RedT sconf_subject wf defass
  have sconf_subject': "sconf_type_ts_ok P ?Es' ts' m'"
    by(auto dest: RedT_invariant_sconf_type)
  { fix t e' x' ln'
    assume es't: "ts' t = \<lfloor>((e', x'), ln')\<rfloor>"
    from sconf_subject' es't obtain E T where ET: "?Es' t = \<lfloor>(E, T)\<rfloor>" by(auto dest!: ts_invD)
    { assume "final e'"
      have "ln' = no_wait_locks"
      proof(rule ccontr)
	assume "ln' \<noteq> no_wait_locks"
	then obtain l where "ln'\<^sub>f l > 0"
	  by(auto simp add: neq_no_wait_locks_conv)
	from lock' es't have "has_locks (ls'\<^sub>f l) t + ln'\<^sub>f l = expr_locks e' l"
	  by(auto dest: lock_okD2)
	with `ln'\<^sub>f l > 0` have "expr_locks e' l > 0" by simp
	moreover from `final e'` have "expr_locks e' l = 0" by(rule final_locks)
	ultimately show False by simp
      qed }
    note ln' = this
    { assume "\<exists>v. e' = Val v"
      then obtain v where v: "e' = Val v" by blast
      with sconf_subject' ET es't have "P,m' \<turnstile> v :\<le> T"
	apply -
	apply(drule ts_invD, assumption)
	by(clarsimp simp add: type_ok_def sconf_type_ok_def conf_def)
      moreover from v ln' have "ln' = no_wait_locks" by(auto)
      ultimately have "\<exists>v. e' = Val v \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,m' \<turnstile> v :\<le> T \<and> ln' = no_wait_locks)"
	using ET v by blast }
    moreover
    { assume "\<exists>a. e' = Throw a"
      then obtain a where a: "e' = Throw a" by blast
      with sconf_subject' ET es't have "\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
	apply -
	apply(drule ts_invD, assumption)
	by(clarsimp simp add: type_ok_def sconf_type_ok_def)
      then obtain T' where "P,E,m' \<turnstile> e' : T'" and "P \<turnstile> T' \<le> T" by blast
      with a have "a \<in> dom m'" by(auto)
      moreover from a ln' have "ln' = no_wait_locks" by(auto)
      ultimately have "\<exists>a. e' = Throw a \<and> a \<in> dom m' \<and> ln' = no_wait_locks"
	using a by blast }
    moreover
    { assume nfine': "\<not> final e'"
      with es't have "final_thread.not_final_thread final_expr s' t"
	by(auto intro: final_thread.not_final_thread.intros)
      with nored have "multithreaded_base.deadlocked final_expr (mred P) s' t"
	by -(erule contrapos_np,rule redT_progress_deadlocked[OF wf addr sconf_subject defass lock RedT])
      moreover 
      from sconf_subject RedT
      have "sconf_type_ts_ok P ?Es' ts' m'"
	by(auto dest: RedT_invariant_sconf_type[OF wf])
      with es't obtain E' T' where "?Es' t = \<lfloor>(E', T')\<rfloor>"
	and "sconf_type_ok P (E', T') e' m' x'"
	by(auto dest!: ts_invD)
      from `sconf_type_ok P (E', T') e' m' x'`
      obtain T'' where "P,E',m' \<turnstile> e' : T''" "P \<turnstile> T'' \<le> T'"
	by(auto simp add: sconf_type_ok_def type_ok_def)
      with `?Es' t = \<lfloor>(E', T')\<rfloor>` have "\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)"
	by blast
      ultimately have "multithreaded_base.deadlocked final_expr (mred P) s' t \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T))" .. }
    ultimately have "(\<exists>v. e' = Val v \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,m' \<turnstile> v :\<le> T) \<and> ln' = no_wait_locks)
                   \<or> (\<exists>a. e' = Throw a \<and> a \<in> dom m' \<and> ln' = no_wait_locks)
                   \<or> multithreaded_base.deadlocked final_expr (mred P) s' t \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T))"
      by(blast) }
  moreover
  have "Es \<unlhd> ?Es'" using esinv RedT
    by -(auto intro: red_mthr.RedT_upd_inv_ext)
  ultimately show "let Es' = upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) ttas\<down>) in
          (\<forall>t e'. \<exists>x' ln'. thr s' t = \<lfloor>((e', x'), ln')\<rfloor> \<longrightarrow>
                    (\<exists>v. e' = Val v \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,shr s' \<turnstile> v :\<le> T) \<and> ln' = no_wait_locks)
                  \<or> (\<exists>a. e' = Throw a \<and> a \<in> dom (shr s') \<and> ln' = no_wait_locks)
                  \<or> multithreaded_base.deadlocked final_expr (mred P) s' t \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,shr s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)))
          \<and> Es \<unlhd> Es'" by(simp)
qed

end