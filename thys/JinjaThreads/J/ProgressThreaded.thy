(*  Title:      JinjaThreads/J/ProgressThreaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Progress and type safety theorem for the multithreaded system} *}

theory ProgressThreaded 
imports 
  Threaded
  TypeSafe
  "../Framework/FWProgress"
begin

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
  def_ass_ts_ok :: "(addr,thread_id,expr \<times> locals) thread_info \<Rightarrow> 'heap \<Rightarrow> bool"
where
  "def_ass_ts_ok \<equiv> ts_ok (\<lambda>t (e, x) h. \<D> e \<lfloor>dom x\<rfloor>)"

context J_heap_base begin

lemma assumes wf: "wf_J_prog P"
  shows red_def_ass_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') c'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<D> e'' \<lfloor>dom x''\<rfloor>"
  
  and reds_def_ass_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') c'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<D> e'' \<lfloor>dom x''\<rfloor>"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  then obtain C fs a where subThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" and ext: "extNTA2J P (C, run, a) = (e'', x'')"
    by(fastsimp dest: red_external_new_thread_sub_thread)
  from sub_Thread_sees_run[OF wf subThread] obtain D pns body
    where sees: "P \<turnstile> C sees run: []\<rightarrow>Void = (pns, body) in D" by auto
  from sees_wf_mdecl[OF wf this] have "\<D> body \<lfloor>{this}\<rfloor>"
    by(auto simp add: wf_mdecl_def)
  with sees ext show ?case by(clarsimp simp del: fun_upd_apply)
qed(auto simp add: ta_upd_simps)

lemma lifting_wf_def_ass: "wf_J_prog P \<Longrightarrow> lifting_wf (mred P) (\<lambda>t (e, x) m. \<D> e \<lfloor>dom x\<rfloor>)"
apply(unfold_locales)
apply(auto dest: red_preserves_defass red_def_ass_new_thread)
done

lemma def_ass_ts_ok_J_start_state:
  "\<lbrakk> wf_J_prog P; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D; length vs = length Ts \<rbrakk> \<Longrightarrow>
  def_ass_ts_ok (thr (J_start_state P C M vs)) h"
apply(rule ts_okI)
apply(drule (1) sees_wf_mdecl)
apply(clarsimp simp add: wf_mdecl_def start_state_def split: split_if_asm)
done

end

subsection {* typeability *}

context J_heap_base begin

definition type_ok :: "J_prog \<Rightarrow> env \<times> ty \<Rightarrow> expr \<Rightarrow> 'heap \<Rightarrow> bool"
where "type_ok P \<equiv> (\<lambda>(E, T) e c. (\<exists>T'. (P,E,c \<turnstile> e : T' \<and> P \<turnstile> T' \<le> T)))"

definition J_sconf_type_ET_start :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> (thread_id \<rightharpoonup> (env \<times> ty))"
where
  "J_sconf_type_ET_start P C M \<equiv>
   let (_, _, T, _) = method P C M
   in ([start_tid \<mapsto> (empty, T)])"

lemma fixes E :: env
  assumes wf: "wf_J_prog P"
  shows red_type_newthread:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>E T. P,E,hp s' \<turnstile> e'' : T \<and> P,hp s' \<turnstile> x'' (:\<le>) E"
  and reds_type_newthread:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; P,E,hp s \<turnstile> es [:] Ts \<rbrakk>
  \<Longrightarrow> \<exists>E T. P,E,hp s' \<turnstile> e'' : T \<and> P,hp s' \<turnstile> x'' (:\<le>) E"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedCallExternal s a U M vs ta va h' ta' e' s')
  from `NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>` `ta' = extTA2J P ta`
  obtain C' M' a' where nt: "NewThread t'' (C', M', a') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
    and "extNTA2J P (C', M', a') = (e'', x'')" by fastsimp
  from red_external_new_thread_sees[OF wf `P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` nt] `typeof_addr (hp s) a = \<lfloor>U\<rfloor>`
  obtain T pns body D where h'a': "typeof_addr h' a' = \<lfloor>Class C'\<rfloor>"
    and sees: " P \<turnstile> C' sees M': []\<rightarrow>T = (pns, body) in D" by auto
  from sees_wf_mdecl[OF wf sees] obtain T where "P,[this \<mapsto> Class D] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "WTrt P (hp s') [this \<mapsto> Class D] body T" by(rule WT_implies_WTrt)
  moreover from sees have "P \<turnstile> C' \<preceq>\<^sup>* D" by(rule sees_method_decl_above)
  with h'a' have "P,h' \<turnstile> [this \<mapsto> Addr a'] (:\<le>) [this \<mapsto> Class D]" by(auto simp add: lconf_def conf_def)
  ultimately show ?case using h'a' sees `s' = (h', lcl s)`
    `extNTA2J P (C', M', a') = (e'', x'')` by(fastsimp intro: sees_method_decl_above)
qed(fastsimp simp add: ta_upd_simps)+

end

context J_heap_conf_base begin

definition sconf_type_ok :: "(env \<times> ty) \<Rightarrow> expr \<Rightarrow> 'heap \<Rightarrow> locals \<Rightarrow> bool" 
where
  "sconf_type_ok ET e h l \<equiv> fst ET \<turnstile> (h, l) \<surd> \<and> type_ok P ET e h"

abbreviation sconf_type_ts_ok :: "(thread_id \<rightharpoonup> (env \<times> ty)) \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<Rightarrow> 'heap \<Rightarrow> bool"
where
  "sconf_type_ts_ok \<equiv> ts_inv (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x)"

lemma ts_inv_ok_J_sconf_type_ET_start:
  "ts_inv_ok (thr (J_start_state P C M vs)) (J_sconf_type_ET_start P C M)"
by(rule ts_inv_okI)(simp add: start_state_def J_sconf_type_ET_start_def split_beta)

end

lemma (in J_heap) red_preserve_welltype:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; P,E,h \<turnstile> e'' : T \<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e'' : T"
by(auto elim: WTrt_hext_mono dest!: red_hext_incr)

lemma (in J_heap_conf) sconf_type_ts_ok_J_start_state:
  "\<lbrakk> wf_J_prog P; start_heap_ok; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D; P,start_heap \<turnstile> vs [:\<le>] Ts \<rbrakk>
  \<Longrightarrow> sconf_type_ts_ok (J_sconf_type_ET_start P C M) (thr (J_start_state P C M vs)) (shr (J_start_state P C M vs))"
apply(rule ts_invI)
apply(simp add: start_state_def split: split_if_asm)
apply(frule (1) sees_wf_mdecl)
apply(auto simp add: wf_mdecl_def J_sconf_type_ET_start_def sconf_type_ok_def sconf_def type_ok_def)
  apply(erule hconf_start_heap)
 apply(erule preallocated_start_heap)
apply(frule list_all2_lengthD)
by(auto simp add: wt_blocks confs_conv_map intro: WT_implies_WTrt)

context J_conf_read begin

lemma red_preserves_type_ok: 
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; wf_J_prog P; E \<turnstile> s \<surd>; type_ok P (E, T) e (hp s) \<rbrakk> \<Longrightarrow> type_ok P (E, T) e' (hp s')"
apply(clarsimp simp add: type_ok_def)
apply(subgoal_tac "\<exists>T''. P,E,hp s' \<turnstile> e' : T'' \<and> P \<turnstile> T'' \<le> T'")
 apply(fast elim: widen_trans)
by(rule subject_reduction)

lemma lifting_inv_sconf_subject_ok:
  assumes wf: "wf_J_prog P"
  shows "lifting_inv (mred P) (\<lambda>t x m. P,m \<turnstile> t \<surd>t) (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x)"
proof(unfold_locales)
  fix t x m ta x' m' i
  assume "mred P t (x, m) ta (x', m')"
    and "(\<lambda>(e, x) m. sconf_type_ok i e m x) x m"
    and tconf: "P,m \<turnstile> t \<surd>t"
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  ultimately have sconf_type: "sconf_type_ok (E, T) e m l"
    and red: "P,t \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>" by auto
  from sconf_type have sconf: "E \<turnstile> (m, l) \<surd>" and "type_ok P (E, T) e m"
    by(auto simp add: sconf_type_ok_def)
  then obtain T' where "P,E,m \<turnstile> e : T'" "P \<turnstile> T' \<le> T" by(auto simp add: type_ok_def)
  from `E \<turnstile> (m, l) \<surd>` `P,E,m \<turnstile> e : T'` red tconf
  have "E \<turnstile> (m', l') \<surd>" by(auto elim: red_preserves_sconf[OF wf])
  moreover
  from red `P,E,m \<turnstile> e : T'` wf `E \<turnstile> (m, l) \<surd>`
  obtain T'' where "P,E,m' \<turnstile> e' : T''" "P \<turnstile> T'' \<le> T'"
    by(auto dest: subject_reduction)
  note `P,E,m' \<turnstile> e' : T''`
  moreover
  from `P \<turnstile> T'' \<le> T'` `P \<turnstile> T' \<le> T`
  have "P \<turnstile> T'' \<le> T" by(rule widen_trans)
  ultimately have "sconf_type_ok (E, T) e' m' l'"
    by(auto simp add: sconf_type_ok_def type_ok_def)
  thus "(\<lambda>(e, x) m. sconf_type_ok i e m x) x' m'" by simp
next
  fix t x m ta x' m' i t'' x''
  assume "mred P t (x, m) ta (x', m')"
    and "(\<lambda>(e, x) m. sconf_type_ok i e m x) x m"
    and tconf: "P,m \<turnstile> t \<surd>t"
    and "NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  moreover obtain e'' l'' where x'' [simp]: "x'' = (e'', l'')" by(cases x'', auto) 
  ultimately have sconf_type: "sconf_type_ok (E, T) e m l"
    and red: "P,t \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>"
    and nt: "NewThread t'' (e'', l'') m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by auto
  from sconf_type have sconf: "E \<turnstile> (m, l) \<surd>" and "type_ok P (E, T) e m"
    by(auto simp add: sconf_type_ok_def)
  then obtain T' where "P,E,m \<turnstile> e : T'" "P \<turnstile> T' \<le> T" by(auto simp add: type_ok_def)
  from nt `P,E,m \<turnstile> e : T'` red have "\<exists>E T. P,E,m' \<turnstile> e'' : T \<and> P,m' \<turnstile> l'' (:\<le>) E"
    by(fastsimp dest: red_type_newthread[OF wf])
  then obtain E'' T'' where "P,E'',m' \<turnstile> e'' : T''" "P,m' \<turnstile> l'' (:\<le>) E''" by blast
  moreover
  from sconf red `P,E,m \<turnstile> e : T'` tconf have "E \<turnstile> (m', l') \<surd>"
    by(auto intro: red_preserves_sconf[OF wf])
  ultimately show "\<exists>i''. (\<lambda>(e, x) m. sconf_type_ok i'' e m x) x'' m'"
    by(auto simp add: sconf_type_ok_def type_ok_def sconf_def)
next
  fix t x m ta x' m' i i'' t'' x''
  assume "mred P t (x, m) ta (x', m')" 
    and "(\<lambda>(e, x) m. sconf_type_ok i e m x) x m" "P,m \<turnstile> t \<surd>t"
    and "(\<lambda>(e, x) m. sconf_type_ok i'' e m x) x'' m" "P,m \<turnstile> t'' \<surd>t"
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  moreover obtain e'' l'' where x'' [simp]: "x'' = (e'', l'')" by(cases x'', auto)
  moreover obtain E'' T'' where i'' [simp]: "i'' = (E'', T'')" by(cases i'', auto)
  ultimately have sconf_type: "sconf_type_ok (E, T) e m l"
    and red: "P,t \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>"
    and sc: "sconf_type_ok (E'', T'') e'' m l''" by auto
  from sconf_type obtain T' where "P,E,m \<turnstile> e : T'" by(auto simp add: sconf_type_ok_def type_ok_def)
  from sc have sconf: "E'' \<turnstile> (m, l'') \<surd>" and "type_ok P (E'', T'') e'' m"
    by(auto simp add: sconf_type_ok_def)
  then obtain T''' where "P,E'',m \<turnstile> e'' : T'''" "P \<turnstile> T''' \<le> T''" by(auto simp add: type_ok_def)
  moreover from red `P,E'',m \<turnstile> e'' : T'''` have "P,E'',m' \<turnstile> e'' : T'''"
    by(rule red_preserve_welltype)
  moreover from sconf red `P,E,m \<turnstile> e : T'` have "hconf m'"
    unfolding sconf_def by(auto dest: red_preserves_hconf[OF wf])
  moreover {
    from red have "hext m m'" by(auto dest: red_hext_incr)
    moreover from sconf have "P,m \<turnstile> l'' (:\<le>) E''" "preallocated m"
      by(simp_all add: sconf_def)
    ultimately have "P,m' \<turnstile> l'' (:\<le>) E''" "preallocated m'"
      by(blast intro: lconf_hext preallocated_hext)+ }
  ultimately have "sconf_type_ok (E'', T'') e'' m' l''"
    by(auto simp add: sconf_type_ok_def sconf_def type_ok_def)
  thus "(\<lambda>(e, x) m. sconf_type_ok i'' e m x) x'' m'" by simp
qed

end

text {* @{term "wf_red"} *}

context J_progress begin

lemma assumes wf: "wf_prog wf_md P"
  shows red_wf_red_aux:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; \<not> red_mthr.actions_ok' (ls, (ts, m), ws) t ta; sync_ok e; hconf (hp s); P,hp s \<turnstile> t \<surd>t;
     \<forall>l. has_locks (ls\<^sub>f l) t \<ge> expr_locks e l;
     ws t = None \<or> 
     (\<exists>a vs w T. call e = \<lfloor>(a, wait, vs)\<rfloor> \<and> typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<and> is_external_call P T wait \<and> ws t = \<lfloor>WokenUp w\<rfloor>) \<rbrakk>
    \<Longrightarrow> \<exists>e'' s'' ta'. P,t \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e'',s''\<rangle> \<and> red_mthr.actions_ok' (ls, (ts, m), ws) t ta' \<and> red_mthr.actions_subset ta' ta"
  (is "\<lbrakk> _; _; _; _; _; _; ?wakeup e s \<rbrakk> \<Longrightarrow> ?concl e s ta")
    and reds_wf_red_aux:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; \<not> red_mthr.actions_ok' (ls, (ts, m), ws) t ta; sync_oks es; hconf (hp s); P,hp s \<turnstile> t \<surd>t;
     \<forall>l. has_locks (ls\<^sub>f l) t \<ge> expr_lockss es l;
     ws t = None \<or> 
     (\<exists>a vs w T. calls es = \<lfloor>(a, wait, vs)\<rfloor> \<and> typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<and> is_external_call P T wait \<and> ws t = \<lfloor>WokenUp w\<rfloor>) \<rbrakk>
    \<Longrightarrow> \<exists>es'' s'' ta'. P,t \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es'',s''\<rangle> \<and> final_thread.actions_ok' (ls, (ts, m), ws) t ta' \<and> final_thread.actions_subset ta' ta"
proof(induct rule: red_reds.inducts)
  case (SynchronizedRed2 e s ta e' s' a)
  note IH = `\<lbrakk>\<not> red_mthr.actions_ok' (ls, (ts, m), ws) t ta; sync_ok e; hconf (hp s); P,hp s \<turnstile> t \<surd>t;
              \<forall>l. expr_locks e l \<le> has_locks (ls\<^sub>f l) t; ?wakeup e s\<rbrakk>
            \<Longrightarrow> ?concl e s ta`
  note `\<not> red_mthr.actions_ok' (ls, (ts, m), ws) t ta`
  moreover from `sync_ok (insync(a) e)` have "sync_ok e" by simp
  moreover note `hconf (hp s)` `P,hp s \<turnstile> t \<surd>t`
  moreover from `\<forall>l. expr_locks (insync(a) e) l \<le> has_locks (ls\<^sub>f l) t`
  have "\<forall>l. expr_locks e l \<le> has_locks (ls\<^sub>f l) t" by(force split: split_if_asm)
  moreover from `?wakeup (insync(a) e) s` have "?wakeup e s" by auto
  ultimately have "?concl e s ta" by(rule IH)
  thus ?case by(fastsimp intro: red_reds.SynchronizedRed2)
next
  case RedCall
  thus ?case
    by(auto simp add: is_val_iff contains_insync_expr_locks_conv contains_insyncs_expr_lockss_conv red_mthr.actions_ok'_empty red_mthr.actions_ok'_ta_upd_obs)
next
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  from `?wakeup (addr a\<bullet>M(map Val vs)) s`
  have "wset (ls, (ts, m), ws) t = None \<or> (M = wait \<and> (\<exists>w. wset (ls, (ts, m), ws) t = \<lfloor>WokenUp w\<rfloor>))" by auto
  with wf  `P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>` `P,hp s \<turnstile> t \<surd>t` `hconf (hp s)` 
  obtain ta'' va' h'' where red': "P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta''\<rightarrow>ext \<langle>va',h''\<rangle>"
    and aoe': "red_mthr.actions_ok' (ls, (ts, m), ws) t ta''"
    and sub: "final_thread.actions_subset ta'' ta" by(rule red_external_wf_red)
  from aoe' have "red_mthr.actions_ok' (ls, (ts, m), ws) t (extTA2J P ta'')"
    by(simp add: red_mthr.actions_ok'_convert_extTA)
  moreover from `ta' = extTA2J P ta` sub
  have "red_mthr.actions_subset (extTA2J P ta'') ta'"
    by(auto del: subsetI elim: final_thread.actions_subset.cases)
  moreover from red' `typeof_addr (hp s) a = \<lfloor>T\<rfloor>` `is_external_call P T M`
  obtain s'' e'' where "P,t \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J P ta''\<rightarrow> \<langle>e'',s''\<rangle>"
    by(fastsimp intro: red_reds.RedCallExternal)
  ultimately show ?case by blast
next
  case LockSynchronized
  hence False by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
  thus ?case ..
next
  case (UnlockSynchronized a v s)
  from `\<forall>l. expr_locks (insync(a) Val v) l \<le> has_locks (ls\<^sub>f l) t`
  have "has_lock (ls\<^sub>f a) t" by(force split: split_if_asm)
  with UnlockSynchronized have False by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
  thus ?case ..
next
  case (SynchronizedThrow2 a ad s)
  from `\<forall>l. expr_locks (insync(a) Throw ad) l \<le> has_locks (ls\<^sub>f l) t`
  have "has_lock (ls\<^sub>f a) t" by(force split: split_if_asm)
  with SynchronizedThrow2 have False
    by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
  thus ?case ..
qed(simp_all add: is_val_iff contains_insync_expr_locks_conv contains_insyncs_expr_lockss_conv red_mthr.actions_ok'_empty red_mthr.actions_ok'_ta_upd_obs split: split_if_asm del: split_paired_Ex, (fastsimp intro: red_reds.intros del: disjE simp del: split_paired_Ex)+)

end

context J_typesafe begin

lemma wf_progress: 
  assumes wf: "wf_J_prog P"
  and "sync_es_ok (thr S) (shr S)"
  and "sconf_type_ts_ok Es (thr S) (shr S)"
  and "thread_conf P (thr S) (shr S)"
  and "lock_ok (locks S) (thr S)"
  and "wset S = empty"
  and "def_ass_ts_ok (thr S) (shr S)"
  shows "progress final_expr (mred P) S"
proof -
  interpret red_mthr!: multithreaded_start final_expr "mred P" S
    using `lock_ok (locks S) (thr S)` `wset S = empty`
    by(unfold_locales)(auto intro: lock_ok_lock_thread_ok wset_thread_okI)
  show ?thesis
  proof
    fix tta s t ex ta e'x' m'
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s"
      and "thr s t = \<lfloor>(ex, no_wait_locks)\<rfloor>"
      and "mred P t (ex, shr s) ta (e'x', m')"
      and wait: "\<not> waiting (wset s t)"
    moreover obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s, auto)
    moreover obtain e x where ex: "ex = (e, x)" by(cases ex, auto)
    moreover obtain e' x' where e'x': "e'x' = (e', x')" by(cases e'x', auto)
    ultimately have tst: "ts t = \<lfloor>(ex, no_wait_locks)\<rfloor>" 
      and red: "P,t \<turnstile> \<langle>e, (m, x)\<rangle> -ta\<rightarrow> \<langle>e', (m', x')\<rangle>" by auto
    from wf have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog)
    from `sync_es_ok (thr S) (shr S)` Red s have aeos: "sync_es_ok ts m"
      by(cases S)(auto dest: RedT_preserves_sync_ok[OF wf])
    with tst ex have aoe: "sync_ok e" by(auto dest: ts_okD)
    from `lock_ok (locks S) (thr S)` `sync_es_ok (thr S) (shr S)` Red s
    have lockok: "lock_ok ls ts" by(cases S)(auto dest: RedT_preserves_lock_ok[OF wf])

    from `sconf_type_ts_ok Es (thr S) (shr S)` Red s `thread_conf P (thr S) (shr S)`
    have "sconf_type_ts_ok (upd_invs Es (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x) (\<down>map (thr_a \<circ> snd) tta\<down>)) ts m"
      by(auto dest: lifting_inv.RedT_invariant[OF lifting_inv_sconf_subject_ok, OF wf])
    with tst ex obtain E T where "sconf_type_ok (E, T) e m x"
      by -((drule ts_invD, assumption),(clarify,blast))
    then obtain T' where "hconf m" "P,E,m \<turnstile> e : T'" "preallocated m"
      by(auto simp add: sconf_type_ok_def sconf_def type_ok_def)
    from Red `thread_conf P (thr S) (shr S)` 
    have "thread_conf P (thr s) (shr s)" by(rule red_tconf.RedT_preserves)
    with `thr s t = \<lfloor>(ex, no_wait_locks)\<rfloor>` have "P,shr s \<turnstile> t \<surd>t" by(auto dest: ts_okD)

    show "\<exists>ta' x' m'. mred P t (ex, shr s) ta' (x', m') \<and> red_mthr.actions_ok' s t ta' \<and> red_mthr.actions_subset ta' ta"
    proof(cases "red_mthr.actions_ok' s t ta")
      case True
      have "red_mthr.actions_subset ta ta" ..
      with True `mred P t (ex, shr s) ta (e'x', m')` show ?thesis by blast
    next
      case False
      from lock_okD2[OF lockok, OF tst[unfolded ex]]
      have locks: "\<forall>l. has_locks (ls\<^sub>f l) t \<ge> expr_locks e l" by simp
      have "ws t = None \<or> (\<exists>a vs w T. call e = \<lfloor>(a, wait, vs)\<rfloor> \<and> typeof_addr (hp (m, x)) a = \<lfloor>T\<rfloor> \<and> is_external_call P T wait \<and> ws t = \<lfloor>WokenUp w\<rfloor>)"
      proof(cases "ws t")
        case None thus ?thesis ..
      next
        case (Some w)
        with red_mthr.in_wait_SuspendD[OF Red `thr s t = \<lfloor>(ex, no_wait_locks)\<rfloor>`, of w] `wset S = empty` ex s
        obtain e0 x0 m0 ta0 w' s1 tta1 
          where red0: "P,t \<turnstile> \<langle>e0, (m0, x0)\<rangle> -ta0\<rightarrow> \<langle>e, (shr s1, x)\<rangle>"
          and Suspend: "Suspend w' \<in> set \<lbrace>ta0\<rbrace>\<^bsub>w\<^esub>" 
          and s1: "P \<turnstile> s1 -\<triangleright>tta1\<rightarrow>* s" by auto
        from red_Suspend_is_call[OF red0 Suspend] obtain a vs T
          where call: "call e = \<lfloor>(a, wait, vs)\<rfloor>"
          and type: "typeof_addr m0 a = \<lfloor>T\<rfloor>" 
          and iec: "is_external_call P T wait" by auto
        from red0 have "m0 \<unlhd> shr s1" by(auto dest: red_hext_incr)
        also from s1 have "shr s1 \<unlhd> shr s" by(rule RedT_hext_incr)
        finally have "typeof_addr (shr s) a = \<lfloor>T\<rfloor>" using type
          by(rule typeof_addr_hext_mono)
        moreover from Some wait s obtain w' where "ws t = \<lfloor>WokenUp w'\<rfloor>"
          by(auto simp add: not_waiting_iff)
        ultimately show ?thesis using call iec s by auto
      qed
      from red_wf_red_aux[OF wf red False[unfolded s] aoe _ _ locks, OF _ _ this] `hconf m` `P,shr s \<turnstile> t \<surd>t` ex s
      show ?thesis by fastsimp
    qed
  next
    fix tta s t x w
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s" 
      and t: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = \<lfloor>WokenUp w\<rfloor>"

    from red_mthr.in_wait_SuspendD[OF Red t, unfolded `wset S = empty`]
    obtain s0 s1 e0 xs0 ta w' e xs
      where x: "x = (e, xs)" 
      and red: "P,t \<turnstile> \<langle>e0, (shr s0, xs0)\<rangle> -ta\<rightarrow> \<langle>e, (shr s1, xs)\<rangle>"
      and Suspend: "Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
      by(cases x) fastsimp
    from red_Suspend_is_call[OF red Suspend] x
    show "\<not> final_expr x" by auto
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
    from `sconf_type_ts_ok Es (thr S) (shr S)` Red s `thread_conf P (thr S) (shr S)`
    have "sconf_type_ts_ok (upd_invs Es (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x) (\<down>map (thr_a \<circ> snd) tta\<down>)) ts m"
      by(auto dest: lifting_inv.RedT_invariant[OF lifting_inv_sconf_subject_ok, OF wf])
    with tst ex obtain E T where "sconf_type_ok (E, T) e m x"
      by -((drule ts_invD, assumption),(clarify,blast))
    then obtain T' where "hconf m" "P,E,m \<turnstile> e : T'" "preallocated m"
      by(auto simp add: sconf_type_ok_def sconf_def type_ok_def)
    moreover
    from `def_ass_ts_ok (thr S) (shr S)` s Red have "def_ass_ts_ok ts m"
      by(cases S)(auto dest: lifting_wf.RedT_preserves[OF lifting_wf_def_ass, OF wf])
    with tst ex have "\<D> e \<lfloor>dom x\<rfloor>" by(auto dest: ts_okD)
    ultimately obtain e' m' x' ta' where "P,t \<turnstile> \<langle>e, (m, x)\<rangle> -ta'\<rightarrow> \<langle>e', (m', x')\<rangle>"
      using nfine by(auto dest: red_progress[OF wwf, where extTA="extTA2J P" and t=t])
    thus "\<exists>ta x' m'. mred P t (ex, shr s) ta (x', m')" using ex s
      by(fastsimp)
  qed
qed

lemma redT_progress_deadlock:
  "\<lbrakk> wf_J_prog P; start_heap_ok; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D; P,start_heap \<turnstile> vs [:\<le>] Ts;
     P \<turnstile> J_start_state P C M vs -\<triangleright>ttas\<rightarrow>* s; final_thread.not_final_thread final_expr s t;
     \<not> red_mthr.deadlock P s\<rbrakk>
  \<Longrightarrow> \<exists>t' ta' s'. P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
apply(rule progress.redT_progress)
   apply(rule wf_progress)
         apply(assumption)+
        apply(rule sync_es_ok_J_start_state, assumption+)
        apply(erule list_all2_lengthD[THEN sym])
       apply(rule sconf_type_ts_ok_J_start_state, assumption+)
      apply(erule thread_conf_start_state)
     apply(rule lock_ok_J_start_state, assumption+)
     apply(erule list_all2_lengthD[THEN sym])
    apply(simp add: start_state_def)
   apply(rule def_ass_ts_ok_J_start_state, assumption+)
   apply(erule list_all2_lengthD)
  apply assumption+
done

lemma redT_progress_deadlocked:
  "\<lbrakk> wf_J_prog P; start_heap_ok; P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D; P,start_heap \<turnstile> vs [:\<le>] Ts;
     P \<turnstile> J_start_state P C M vs -\<triangleright>ttas\<rightarrow>* s; final_thread.not_final_thread final_expr s t;
     \<not> red_mthr.deadlocked P s t\<rbrakk>
  \<Longrightarrow> \<exists>t' ta' s'. P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
apply(rule progress.redT_progress_deadlocked')
   apply(rule wf_progress)
         apply(assumption)+
        apply(rule sync_es_ok_J_start_state, assumption+)
        apply(erule list_all2_lengthD[THEN sym])
       apply(rule sconf_type_ts_ok_J_start_state, assumption+)
      apply(erule thread_conf_start_state)
     apply(rule lock_ok_J_start_state, assumption+)
     apply(erule list_all2_lengthD[THEN sym])
    apply(simp add: start_state_def)
   apply(rule def_ass_ts_ok_J_start_state, assumption+)
   apply(erule list_all2_lengthD)
  apply assumption+
apply(auto simp add: red_mthr.deadlocked'_def)
done

section {* Type safety proof *}

theorem TypeSafetyT:
  fixes C and M and ttas and Es
  defines "Es  == J_sconf_type_ET_start P C M"
  and     "Es' == upd_invs Es (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x) (\<down>map (thr_a \<circ> snd) ttas\<down>)"
  assumes wf: "wf_J_prog P"
  and start_heap: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  and RedT: "P \<turnstile> J_start_state P C M vs -\<triangleright>ttas\<rightarrow>* s'"
  and nored: "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow> s'')"
  shows "thread_conf P (thr s') (shr s')"
  and "thr s' t = \<lfloor>((e', x'), ln')\<rfloor> \<Longrightarrow>
       (\<exists>v. e' = Val v \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,shr s' \<turnstile> v :\<le> T) \<and> ln' = no_wait_locks)
       \<or> (\<exists>a C. e' = Throw a \<and> typeof_addr (shr s') a = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable \<and> ln' = no_wait_locks)
       \<or> (red_mthr.deadlocked P s' t \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,shr s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)))"
     (is "_ \<Longrightarrow> ?thesis2")
  and "Es \<subseteq>\<^sub>m Es'"
proof -
  from RedT show "thread_conf P (thr s') (shr s')"
    by(rule red_tconf.RedT_preserves)(rule thread_conf_start_state[OF start_heap])
next
  show "Es \<subseteq>\<^sub>m Es'" using RedT ts_inv_ok_J_sconf_type_ET_start
    unfolding Es'_def Es_def by(rule red_mthr.RedT_upd_inv_ext)
next
  assume "thr s' t = \<lfloor>((e', x'), ln')\<rfloor>"
  moreover obtain ls' ts' m' ws' where s' [simp]: "s' = (ls', (ts', m'), ws')" by(cases s', auto)
  ultimately have es't: "ts' t = \<lfloor>((e', x'), ln')\<rfloor>" by simp
  from wf have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog)
  from conf have len: "length vs = length Ts" by(rule list_all2_lengthD)
  from RedT def_ass_ts_ok_J_start_state[OF wf sees len] have defass': "def_ass_ts_ok ts' m'"
    by(fastsimp dest: lifting_wf.RedT_preserves[OF lifting_wf_def_ass, OF wf])
  from RedT sync_es_ok_J_start_state[OF wf sees len[symmetric]] lock_ok_J_start_state[OF wf sees len[symmetric]]
  have lock': "lock_ok ls' ts'" by (fastsimp dest: RedT_preserves_lock_ok[OF wf])
  from RedT sync_es_ok_J_start_state[OF wf sees len[symmetric]] have addr': "sync_es_ok ts' m'"
    by(fastsimp dest: RedT_preserves_sync_ok[OF wf])
  from RedT sconf_type_ts_ok_J_start_state[OF wf start_heap sees conf] start_heap
  have sconf_subject': "sconf_type_ts_ok Es' ts' m'" unfolding Es'_def Es_def
    by(fastsimp dest: lifting_inv.RedT_invariant[OF lifting_inv_sconf_subject_ok, OF wf] intro: thread_conf_start_state)
  with es't obtain E T where ET: "Es' t = \<lfloor>(E, T)\<rfloor>" 
    and "sconf_type_ok (E, T) e' m' x'" by(auto dest!: ts_invD)
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
      by(auto dest: ts_invD simp add: type_ok_def sconf_type_ok_def conf_def)
    moreover from v ln' have "ln' = no_wait_locks" by(auto)
    ultimately have "\<exists>v. e' = Val v \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,m' \<turnstile> v :\<le> T \<and> ln' = no_wait_locks)"
      using ET v by blast }
  moreover
  { assume "\<exists>a. e' = Throw a"
    then obtain a where a: "e' = Throw a" by blast
    with sconf_subject' ET es't have "\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
      apply -
      apply(drule ts_invD, assumption)
      by(clarsimp simp add: type_ok_def sconf_type_ok_def)
    then obtain T' where "P,E,m' \<turnstile> e' : T'" and "P \<turnstile> T' \<le> T" by blast
    with a have "\<exists>C. typeof_addr m' a = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable"
      by(auto simp add: widen_Class dest: typeof_addr_eq_Some_conv)
    moreover from a ln' have "ln' = no_wait_locks" by(auto)
    ultimately have "\<exists>a C. e' = Throw a \<and> typeof_addr m' a = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable \<and> ln' = no_wait_locks"
      using a by blast }
  moreover
  { assume nfine': "\<not> final e'"
    with es't have "red_mthr.not_final_thread s' t"
      by(auto intro: red_mthr.not_final_thread.intros)
    with nored have "red_mthr.deadlocked P s' t"
      by -(erule contrapos_np, rule redT_progress_deadlocked[OF wf start_heap sees conf RedT])
    moreover 
    from `sconf_type_ok (E, T) e' m' x'`
    obtain T'' where "P,E,m' \<turnstile> e' : T''" "P \<turnstile> T'' \<le> T"
      by(auto simp add: sconf_type_ok_def type_ok_def)
    with ET have "\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)"
      by blast
    ultimately have "red_mthr.deadlocked P s' t \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T))" .. }
  ultimately show ?thesis2 by simp(blast)
qed

end

end