(*  Title:      JinjaThreads/J/ProgressThreaded.thy
    Author:     Andreas Lochbihler
*)

theory ProgressThreaded 
imports Threaded TypeSafe "../Framework/FWProgress"
begin

text {* translating syntax *}

syntax
  can_sync_syntax :: "J_prog \<Rightarrow> expr \<Rightarrow> heap \<times> locals \<Rightarrow> addr set \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>" [50,0,0,0] 81)

translations
  "P \<turnstile> \<langle>e, s\<rangle> L \<wrong>" => "multithreaded.can_sync ((CONST mred) P) (e, snd s) (fst s) L"
  "P \<turnstile> \<langle>e, (h, x)\<rangle> L \<wrong>" == "multithreaded.can_sync ((CONST mred) P) (e, x) h L"

syntax
  must_sync_syntax :: "J_prog \<Rightarrow> expr \<Rightarrow> heap \<times> locals \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>" [50,0,0] 81)

translations
  "P \<turnstile> \<langle>e, s\<rangle> \<wrong>" => "multithreaded.must_sync ((CONST mred) P) (e, snd s) (fst s)"
  "P \<turnstile> \<langle>e, (h, x)\<rangle> \<wrong>" == "multithreaded.must_sync ((CONST mred) P) (e, x) h"


text {* Interpreting final\_thread\_wf with final *}

lemma final_no_red [elim]:
  "final e \<Longrightarrow> \<not> P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>"
apply(auto elim: red.cases finalE)
done

lemma final_locks: "final e \<Longrightarrow> expr_locks e l = 0"
by(auto elim: finalE)

lemma final_thread_wf_interp: "final_thread_wf final_expr (mred P)"
proof(unfold_locales)
  fix x m ta x' m'
  assume "final_expr x" "mred P (x, m) ta (x', m')"
  moreover obtain e l where e: "x = (e, l)" by (cases x, auto)
  ultimately have "final e" by simp
  moreover obtain e' l' where e': "(x' :: char list exp \<times> (char list \<rightharpoonup> val)) = (e', l')" by (cases x', auto)
  ultimately show "False" using e `mred P (x, m) ta (x', m')` by(auto)
qed

interpretation red_mthr_final: final_thread_wf ["final_expr" "mred P"]
by(rule final_thread_wf_interp)

lemma lock_ok_ls_Some_ex_ts_not_final:
  assumes lock: "lock_ok ls ts"
  and hl: "has_lock (ls l) t"
  shows "\<exists>e x ln. ts t = \<lfloor>((e, x), ln)\<rfloor> \<and> \<not> final e"
proof -
  from lock have "lock_thread_ok ls ts"
    by(rule lock_ok_lock_thread_ok)
  with hl obtain e x ln
    where tst: "ts t = \<lfloor>((e, x), ln)\<rfloor>"
    by(auto dest!: lock_thread_okD)
  { assume "final e"
    hence "expr_locks e l = 0" by(rule final_locks)
    with lock tst have "has_locks (ls l) t = 0"
      by(auto dest: lock_okD2[rule_format, where l=l])
    with hl have False by simp }
  with tst show ?thesis by auto
qed


text {* Preservation lemmata *}

text {* Definite assignment *}


abbreviation
  def_ass_ts_ok :: "(addr,thread_id,expr \<times> locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "def_ass_ts_ok \<equiv> ts_ok (\<lambda>(e, x) h. \<D> e \<lfloor>dom x\<rfloor>)"

lemma red_def_ass_new_thread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') c'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<D> e'' \<lfloor>dom x''\<rfloor>"
apply(induct rule: red.induct)
apply(auto)
apply(simp add: hyper_isin_def)
done

lemma lifting_wf_def_ass: "wf_J_prog P \<Longrightarrow> lifting_wf (mred P) (\<lambda>(e, x) m. \<D> e \<lfloor>dom x\<rfloor>)"
apply(unfold_locales)
apply(auto dest: red_preserves_defass red_def_ass_new_thread)
done

lemmas redT_preserves_defass = lifting_wf.redT_preserves[OF lifting_wf_def_ass]
lemmas RedT_preserves_defass = lifting_wf.RedT_preserves[OF lifting_wf_def_ass]

text {* lock\_thread\_ok *}

lemma preserves_lock_thread_ok:
  "\<lbrakk> wf_J_prog P; lock_ok (locks s) (thr s); sync_es_ok (thr s) (shr s) \<rbrakk> \<Longrightarrow> preserves_lock_thread_ok final_expr (mred P) s"
apply(unfold_locales)
apply(rule lock_ok_lock_thread_ok)
by(rule RedT_preserves_lock_ok)

text {* typeability *}

lemma NewThread_is_class_Thread: 
  assumes wf: "wf_J_prog P"
  and major: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
  and minor: "sconf P E s" "P,E,hp s \<turnstile> e:T" "NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "is_class P Thread"
using major minor
proof(induct arbitrary: E T rule: red.induct)
  case (CallParams e s ta e' s' v M vs es E T)
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T; NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<rbrakk> \<Longrightarrow> is_class P Thread" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> Val v\<bullet>M(map Val vs @ e # es) : T" by fact
  have ta: "NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by fact
  from wt have "\<exists>T. P,E,hp s \<turnstile> e : T"
    by(fastsimp elim: WTrt_elim_cases simp add: list_all2_append1 list_all2_Cons1)+
  then obtain T where "P,E,hp s \<turnstile> e : T" by blast
  thus ?case by -(rule IH[OF conf _ ta])
next
  case (RedNewThread s a C fs E T)
  have hpsa: "hp s a = \<lfloor>Obj C fs\<rfloor>" by fact
  have PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> addr a\<bullet>start([]) : T" by fact
  note ta = `NewThread t'' (e'', l'') h'' \<in> set \<lbrace>\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a (Var this\<bullet>run([]), [this \<mapsto> Addr a]) (hp s)\<rbrace>\<rbrace>\<^bsub>t\<^esub>`
  from conf hpsa have "is_class P C" by(force simp add: sconf_def hconf_def oconf_def)
  thus ?case
    by(auto intro: converse_subcls_is_class[OF wf PCThread])
next
  case (BlockRedNone e h l V ta e' h' l' T E T')
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h, l(V := None)) \<surd>; P,E,hp (h, l(V := None)) \<turnstile> e : T; NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<rbrakk> \<Longrightarrow> is_class P Thread" by fact
  have conf: "P,E \<turnstile> (h, l) \<surd>" by fact
  have wt: "P,E,hp (h, l) \<turnstile> {V:T; e} : T'" by fact
  have ta: "NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by fact
  from conf have conf': "P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>"
    by(clarsimp simp add: sconf_def lconf_def)
  thus ?case using wt ta by -(erule IH, simp_all)
next
  case (BlockRedSome e h l V ta e' h' l' v T E T')
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h, l(V := None)) \<surd>; P,E,hp (h, l(V := None)) \<turnstile> e : T; NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<rbrakk> \<Longrightarrow> is_class P Thread" by fact
  have conf: "P,E \<turnstile> (h, l) \<surd>" by fact
  have wt: "P,E,hp (h, l) \<turnstile> {V:T; e} : T'" by fact
  have ta: "NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by fact
  from conf have conf': "P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>"
    by(clarsimp simp add: sconf_def lconf_def)
  thus ?case using wt ta by -(erule IH, simp_all)
next
  case (InitBlockRed e h l V v ta e' h' l' v' T E T')
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h, l(V \<mapsto> v)) \<surd>; P,E,hp (h, l(V \<mapsto> v)) \<turnstile> e : T; NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<rbrakk> \<Longrightarrow> is_class P Thread" by fact
  have conf: "P,E \<turnstile> (h, l) \<surd>" by fact
  have wt: "P,E,hp (h, l) \<turnstile> {V:T := Val v; e} : T'" by fact
  have v': "l' V = Some v'" by fact
  have ta: "NewThread t'' (e'', l'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by fact
  from wt obtain T\<^isub>1 where wt\<^isub>1: "typeof\<^bsub>h\<^esub> v = Some T\<^isub>1"
    and T1subT: "P \<turnstile> T\<^isub>1 \<le> T" and wt\<^isub>2: "P,E(V\<mapsto>T),h \<turnstile> e : T'" by auto
  with conf have conf': "P,E(V \<mapsto> T) \<turnstile> (h, l(V \<mapsto> v)) \<surd>"
    by(clarsimp simp add: sconf_def lconf_def conf_def)
  thus ?case apply (rule IH) apply simp apply (rule wt\<^isub>2) apply (rule ta) done
qed(fastsimp)+


constdefs
  type_ok :: "J_prog \<Rightarrow> env \<times> ty \<Rightarrow> expr \<Rightarrow> heap \<Rightarrow> bool"
  "type_ok P \<equiv> (\<lambda>(E, T) e c. (\<exists>T'. (P,E,c \<turnstile> e : T' \<and> P \<turnstile> T' \<le> T)))"

lemma red_preserves_type_ok: "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; wf_J_prog P; P,E \<turnstile> s \<surd>; type_ok P (E, T) e (hp s) \<rbrakk> \<Longrightarrow> type_ok P (E, T) e' (hp s')"
apply(clarsimp simp add: type_ok_def)
apply(subgoal_tac "\<exists>T''. P,E,hp s' \<turnstile> e' : T'' \<and> P \<turnstile> T'' \<le> T'")
 apply(fast elim: widen_trans)
by(rule subject_reduction)

lemma red_preserve_welltype:
  "\<lbrakk> P \<turnstile> \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; P,E,h \<turnstile> e'' : T \<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e'' : T"
by(auto elim: WTrt_hext_mono dest!: red_hext_incr)

definition sconf_type_ok :: "J_prog \<Rightarrow> (env \<times> ty) \<Rightarrow> expr \<Rightarrow> heap \<Rightarrow> locals \<Rightarrow> bool" where
  "sconf_type_ok P ET e h l \<equiv> P,fst ET \<turnstile> (h, l) \<surd> \<and> type_ok P ET e h"

abbreviation
  sconf_type_ts_ok :: "J_prog \<Rightarrow> (thread_id \<rightharpoonup> (env \<times> ty)) \<Rightarrow> (addr,thread_id,expr \<times> locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "sconf_type_ts_ok \<equiv> \<lambda>P. ts_inv (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x)"

lemma red_sconf_type_newthread:
  assumes wf: "wf_J_prog P"
  and red: "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  and ta: "NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  and wt: "P,E,hp s \<turnstile> e : T"
  and sconf: "P,(E::env) \<turnstile> s \<surd>"
  shows "\<exists>E T. P,E,hp s' \<turnstile> e'' : T \<and> P,hp s' \<turnstile> x'' (:\<le>) E"
proof -
  from assms have isclassThread: "is_class P Thread"
    by(auto intro!: NewThread_is_class_Thread)
  from red ta wt show ?thesis
  proof(induct arbitrary: E T rule: red.induct)
    case (RedNewThread s a C fs E T)
    have wt: "P,E,hp s \<turnstile> addr a\<bullet>start([]) : T" by fact
    have hpsa: "hp s a = \<lfloor>Obj C fs\<rfloor>" by fact
    have PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" by fact
    note `NewThread t'' (e'', x'') (hp s) \<in> set \<lbrace>\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a (Var this\<bullet>run([]), [this \<mapsto> Addr a]) (hp s)\<rbrace>\<rbrace>\<^bsub>t\<^esub>`
    hence NT: "NewThread a (Var this\<bullet>run([]), [this \<mapsto> Addr a]) (hp s)  = NewThread t'' (e'', x'') (hp s)" by simp
    have "\<exists>D mthd. P \<turnstile> C sees run: []\<rightarrow>Void = mthd in D"
      by(rule sub_Thread_sees_run[OF wf PCThread isclassThread])
    hence "(P,[this \<mapsto> Class C],hp s \<turnstile> Var this\<bullet>run([]) : Void)"
      by(auto intro: WTrtCall WTrtVar)
    moreover have "(P,hp s \<turnstile> [this \<mapsto> Addr a] (:\<le>) [this \<mapsto> Class C])" using hpsa
      by(simp add: lconf_def)
    ultimately show ?case using NT
      apply(clarsimp)
      apply(rule_tac x="[this \<mapsto> Class C]" in exI)
      apply(clarsimp)
      by(rule_tac x="Void" in exI)
  qed(fastsimp simp add: list_all2_append1 list_all2_Cons1)+
qed

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
  from red nt `P,E,m \<turnstile> e : T'` `P,E \<turnstile> (m, l) \<surd>`
  have "\<exists>E T. P,E,m' \<turnstile> e'' : T \<and> P,m' \<turnstile> l'' (:\<le>) E"
    by(fastsimp dest: red_sconf_type_newthread[OF wf])
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

lemmas RedT_preserves_es_inv_ok = multithreaded.RedT_preserves_ts_inv_ok[where r="mred P"]

text {* wf\_red *}

lemma red_new_thread_heap:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' ex'' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = hp s'"
by(induct rule: red.induct)(auto)

lemma red_Unlock_no_wait_Unlock: 
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [] \<rbrakk>
  \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock]"
by(induct rule: red.induct)(fastsimp split: split_if_asm)+

lemma red_UnlockFail_UnlockFail:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l) \<rbrakk>
  \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
by(induct rule: red.induct)(fastsimp split: split_if_asm)+

lemma red_wait_at_most_one:
  "P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow>
   \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [] \<or> (\<exists>a. \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend a]) \<or> 
   (\<exists>a. \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Notify a]) \<or> (\<exists>a. \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [NotifyAll a])"
by(induct rule: red.induct)(auto)

lemma red_wait_at_most_oneE [consumes 1, case_names Nil Suspend Notify NotifyAll]:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [] \<Longrightarrow> thesis;
    \<And>a. \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend a] \<Longrightarrow> thesis; 
    \<And>a. \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Notify a] \<Longrightarrow> thesis;
    \<And>a. \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [NotifyAll a] \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(drule red_wait_at_most_one, auto)

lemma red_lock_at_most_one:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l' = las; las \<noteq> [] \<rbrakk> 
  \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>l. [])(l' := las)"
by(induct arbitrary: l' las rule: red.induct)(fastsimp)+

lemma red_notify_conv:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Notify l] \<rbrakk>
  \<Longrightarrow> ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub> Notify l \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l \<rbrace>"
by(induct rule: red.induct)(fastsimp split: split_if_asm)+

lemma red_notifyAll_conv:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [NotifyAll l] \<rbrakk>
  \<Longrightarrow> ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub> NotifyAll l \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l \<rbrace>"
by(induct rule: red.induct)(fastsimp split: split_if_asm)+

lemma red_suspend_conv:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [Suspend l] \<rbrakk>
  \<Longrightarrow> ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub> Suspend l \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l, ReleaseAcquire\<rightarrow>l \<rbrace>"
by(induct rule: red.induct)(fastsimp)+

lemma red_unlock_no_wait_expr_locks:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
     Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l); \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [] \<rbrakk>
  \<Longrightarrow> expr_locks e l > 0"
by(induct rule: red.induct)(fastsimp split: split_if_asm)+

lemma red_Unlock_Lock_no_lock_ex_UnlockFail:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las \<rbrakk>
  \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  case (RedWait s a arrobj)
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las`
  hence "a = l" by(simp split: split_if_asm)
  with `hp s a = \<lfloor>arrobj\<rfloor>` show ?case
    by(fastsimp intro: RedWaitFail)
next
  case (RedNotify s a arrobj)
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>w\<^esub>Notify a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las`
  hence "a = l" by(simp split: split_if_asm)
  with `hp s a = \<lfloor>arrobj\<rfloor>` show ?case
    by(fastsimp intro: RedNotifyFail)
next
  case (RedNotifyAll s a arrobj)
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>w\<^esub>NotifyAll a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las`
  hence "a = l" by(simp split: split_if_asm)
  with `hp s a = \<lfloor>arrobj\<rfloor>` show ?case
    by(fastsimp intro: RedNotifyAllFail)
next
  case (BlockRedNone e h x V ta e' h' l' T)
  note IH = `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las` obtain e' s'
    where "P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by fastsimp
  moreover
  then obtain h' x' where "s' = (h', x')" by (cases s', auto)
  ultimately show ?case using `\<not> assigned V e`
    apply(cases "x' V")
     apply(fastsimp intro: red.BlockRedNone)
    by(fastsimp intro: red.BlockRedSome)
next
  case (BlockRedSome e h x V ta e' h' l' v T)
  note IH = `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las` obtain e' s'
    where red: "P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by fastsimp
  moreover
  then obtain h' x' where "s' = (h', x')" by (cases s', auto)
  ultimately show ?case using `\<not> assigned V e`
    apply(cases "x' V")
     apply(fastsimp intro: red.BlockRedNone)
    by(fastsimp intro: red.BlockRedSome)
next
  case (InitBlockRed e h x V v ta e' h' x' v' T)
  from `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
    `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] @ las`
  obtain e' s'
    where red: "P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by fastsimp
  moreover
  then obtain h' x' where s': "s' = (h', x')" by (cases s', auto)
  ultimately have "\<exists>v. x' V = \<lfloor>v\<rfloor>"
    by(auto dest!: red_lcl_incr)
  with red s' show ?case
    by(fastsimp intro: red.InitBlockRed)
qed(fastsimp intro: red.intros split: split_if_asm)+

lemma red_UnlockFail_ex_Unlock:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail] \<rbrakk>
  \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l, ReleaseAcquire\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub> Suspend l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>
           \<or> P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub> Notify l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>
           \<or> P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub> NotifyAll l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  case (RedWaitFail s a arrobj)
  note h = `hp s a = \<lfloor>arrobj\<rfloor>`
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  hence "a = l" by(auto split: split_if_asm)
  with h show ?case
    by -(drule RedWait, fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else split: split_if_asm)
next
  case (RedNotifyFail s a arrobj)
  note h = `hp s a = \<lfloor>arrobj\<rfloor>`
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  hence "a = l" by(auto split: split_if_asm)
  with h show ?case
    by -(drule RedNotify, fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else split: split_if_asm)
next
  case (RedNotifyAllFail s a arrobj)
  note h = `hp s a = \<lfloor>arrobj\<rfloor>`
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`
  hence "a = l" by(auto split: split_if_asm)
  with h show ?case
    by -(drule RedNotifyAll, fastsimp simp add: fun_upd_def if_else_if_else_eq_if_else split: split_if_asm)
next
  case (BlockRedNone e h x V ta e' h' l' T)
  let "?c e' s'" = "P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l, ReleaseAcquire\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Suspend l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle> \<or>
                    P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle> \<or>
                    P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
  from `\<lbrakk> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail] \<rbrakk> \<Longrightarrow> \<exists>e' s'. ?c e' s'`[OF `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`]
  obtain e' s' where "?c e' s'" by blast
  moreover
  obtain h' x' where "s' = (h', x')" by (cases s', auto)
  moreover note `\<not> assigned V e`
  ultimately show ?case
    apply(cases "lcl s' V")
     apply(fastsimp simp add: fun_upd_def intro: red.BlockRedNone)
    apply(fastsimp simp add: fun_upd_def intro: red.BlockRedSome)
    done
next
  case (BlockRedSome e h x V ta e' h' l' v T)
  let "?c e' s'" = "P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l, ReleaseAcquire\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Suspend l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle> \<or>
                    P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle> \<or>
                    P \<turnstile> \<langle>e,(h, x(V := None))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
  from `\<lbrakk> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail] \<rbrakk> \<Longrightarrow> \<exists>e' s'. ?c e' s'`[OF `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`]
  obtain e' s' where "?c e' s'" by blast 
  moreover
  obtain h' x' where "s' = (h', x')" by (cases s', auto)
  moreover note `\<not> assigned V e`
  ultimately show ?case
    apply(cases "lcl s' V")
     apply(fastsimp simp add: fun_upd_def intro: red.BlockRedNone)
    apply(fastsimp simp add: fun_upd_def intro: red.BlockRedSome)
    done
next
  case (InitBlockRed e h x V v ta e' h' l' v' T)
  let "?c e' s'" = "P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l, ReleaseAcquire\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Suspend l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle> \<or>
                    P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle> \<or>
                    P \<turnstile> \<langle>e,(h, x(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
  from `\<lbrakk> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail] \<rbrakk> \<Longrightarrow> \<exists>e' s'. ?c e' s'`[OF `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]`]
  obtain e' s' where red: "?c e' s'" by blast 
  moreover
  obtain h' x' where "s' = (h', x')" by (cases s') auto
  moreover
  from red have "\<exists>v. lcl s' V = \<lfloor>v\<rfloor>"
    by(auto dest!: red_lcl_incr)
  ultimately show ?case
    by(fastsimp simp add: fun_upd_def intro: red.InitBlockRed)
qed(fastsimp intro: red.intros simp add: split: split_if_asm)+

lemma red_thread_at_most_one:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> [] \<rbrakk>
  \<Longrightarrow> \<exists>t. (\<exists>e x. ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread t (e, x) (hp s')\<rbrace>) \<or> ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists t\<rbrace>"
by(induct rule: red.induct)(auto)

lemma red_thread_at_most_oneE [consumes 2, case_names NewThreadFail NewThread]:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> [];
     \<And>t e x. ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread t (e, x) (hp s')\<rbrace> \<Longrightarrow> thesis;
     \<And>t. ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists t\<rbrace> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
by(drule red_thread_at_most_one)(auto)

lemma red_NewThreadFail_NewThread:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [ThreadExists t] \<rbrakk> 
  \<Longrightarrow> \<exists>e' s' e'' x''. P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread t (e'', x'') (hp s')\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  case (RedNewThreadFail s a C fs)
  from `\<lbrace>\<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists a\<rbrace>\<rbrace>\<^bsub>t\<^esub> = [ThreadExists t]`
  have "t = a" by simp
  with `P \<turnstile> C \<preceq>\<^sup>* Thread` `hp s a = \<lfloor>Obj C fs\<rfloor>`
  show ?case by(fastsimp intro: red.RedNewThread)
next
  case (BlockRedNone e h l V ta e' h' l' T)
  thus ?case
    apply(clarsimp)
    apply(case_tac "b V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next
  case (BlockRedSome e h l V ta e' h' l' v T)
  thus ?case
    apply(clarsimp)
    apply(case_tac "b V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next
  case (InitBlockRed e h l V v ta e' h' l' v' T)
  from `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [ThreadExists t]`
    `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [ThreadExists t] \<Longrightarrow> \<exists>e' s' e'' x''. P \<turnstile> \<langle>e,(h, l(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread t (e'', x'') (hp s')\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>`
  obtain e' s' e'' x''
    where red: "P \<turnstile> \<langle>e,(h, l(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread t (e'', x'') (hp s')\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>"
    by blast
  moreover obtain h' l' where "s' = (h', l')" by (cases s', auto)
  moreover with red have "\<exists>v. l' V = \<lfloor>v\<rfloor>"
    by(auto dest!: red_lcl_incr)
  ultimately show ?case
    by(fastsimp intro: red.InitBlockRed)
qed(fastsimp intro: red.intros)+

lemma red_NewThread_NewThreadFail:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') (hp s')] \<rbrakk> \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists t\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
proof(induct rule: red.induct)
  case (RedNewThread s a C fs)
  note `\<lbrace>\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a (Var this\<bullet>run([]), [this \<mapsto> Addr a]) (hp s)\<rbrace>\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') (hp s)]`
  hence ta: "a = t"
    and e'': "e'' = Var this\<bullet>run([])"
    and x'': "x'' = [this \<mapsto> Addr a]" by auto
  with `hp s a = \<lfloor>Obj C fs\<rfloor>` `P \<turnstile> C \<preceq>\<^sup>* Thread`
  show ?case by(fastsimp intro: red.RedNewThreadFail)
next
  case (BlockRedNone e h l V ta e' h' l' T)
  thus ?case
    apply(clarsimp)
    apply(case_tac "b V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next
  case (BlockRedSome e h l V ta e' h' l' v T)
  thus ?case
    apply(clarsimp)
    apply(case_tac "b V")
    by(fastsimp intro: red.BlockRedNone red.BlockRedSome)+
next
  case (InitBlockRed e h l V v ta e' h' l' v' T)
  from `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') (hp (h', l'(V := l V)))]`
    `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [NewThread t (e'', x'') (hp (h', l'))] \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e, (h, l(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists t\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>`
  obtain e' h' l' where "P \<turnstile> \<langle>e, (h, l(V \<mapsto> v))\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists t\<rbrace>\<rightarrow> \<langle>e', (h', l')\<rangle>" by fastsimp
  moreover then obtain v' where "l' V = \<lfloor>v'\<rfloor>" by(auto dest!: red_lcl_incr)
  ultimately show ?case by(fastsimp intro: red.InitBlockRed)
qed(fastsimp intro:red.intros)+


lemma red_wf_red:
  assumes wf: "wf_J_prog P"
  and "sync_es_ok (thr S) (shr S)"
  and "lock_ok (locks S) (thr S)"
  and "sconf_type_ts_ok P Es (thr S) (shr S)"
  shows "wf_red final_expr (mred P) S"
proof(unfold_locales)
  fix tta s t ex ta e'x' m'
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s"
    and "thr s t = \<lfloor>(ex, no_wait_locks)\<rfloor>"
    and "mred P (ex, shr s) ta (e'x', m')"
  moreover obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s) auto
  moreover obtain e x where ex: "ex = (e, x)" by(cases ex) auto
  moreover obtain e' x' where e'x': "e'x' = (e', x')" by(cases e'x') auto
  ultimately have tst: "ts t = \<lfloor>(ex, no_wait_locks)\<rfloor>" 
    and red: "P \<turnstile> \<langle>e, (m, x)\<rangle> -ta\<rightarrow> \<langle>e', (m', x')\<rangle>" by auto
  from wf have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog)
  from `sync_es_ok (thr S) (shr S)` Red s have aeos: "sync_es_ok ts m"
    by(cases S)(auto dest: RedT_preserves_sync_ok[OF wf])
  with tst ex have aoe: "sync_ok e" by(auto dest: ts_okD)
  from `lock_ok (locks S) (thr S)` `sync_es_ok (thr S) (shr S)` Red s
  have lockok: "lock_ok ls ts" by(cases S)(auto dest: RedT_preserves_lock_ok[OF wf])
  from `sconf_type_ts_ok P Es (thr S) (shr S)` Red s
  have "sconf_type_ts_ok P (upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) tta\<down>)) ts m"
    by(cases S)(auto dest: RedT_invariant_sconf_type[OF wf])
  with tst ex obtain E T where "sconf_type_ok P (E, T) e m x"
    by -((drule ts_invD, assumption),(clarify,blast))
  hence hconf: "P \<turnstile> m \<surd>" by(simp add: sconf_type_ok_def sconf_def)

  have "\<exists>ta' e'x' m'. mred P (ex, m) ta' (e'x', m') \<and> thread_oks ts m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> 
                      lock_ok_las' ls t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> 
                      red_mthr.cond_action_oks' (ls, (ts, m), ws) t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and>
                      red_mthr.collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> red_mthr.collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
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
	and lao': "\<And>xs ys. \<lbrakk> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ Lock # ys; lock_actions_ok (ls l) t xs \<rbrakk>
                   \<Longrightarrow> may_lock (upd_locks (ls l) t xs) t"
	by(auto simp only: not_lock_actions_ok'_conv)
      from nlaos obtain xs L ys
	where tal: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys"
	and loa: "lock_actions_ok (ls l) t xs"
	and nlao: "\<not> lock_action_ok (upd_locks (ls l) t xs) t L"
	by(auto simp only: not_lock_actions_ok_conv)
      from nlao show ?thesis
      proof(induct rule: not_lock_action_okE)
	case Lock
	with tal loa have False
	  by(auto simp del: locks_a_def dest: lao')
	thus ?thesis by simp
      next
	case Unlock
	note L = `L = Unlock`
	note nhl = `\<not> has_lock (upd_locks (ls l) t xs) t`
	with tal L have unlocktal: "Unlock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)" by simp
	from red show ?thesis
	proof(induct rule: red_wait_at_most_oneE)
	  case Nil
	  with red unlocktal have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock]"
	    by(rule red_Unlock_no_wait_Unlock)
	  with tal L have xs: "xs = []" and ys: "ys = []"
	    by(auto simp add: Cons_eq_append_conv append_eq_Cons_conv)
	  with nhl have nhl: "\<not> has_lock (ls l) t" by simp
	  with tst ex lockok have "expr_locks e l = 0"
	    by(auto dest: lock_okD2)
	  moreover
	  from aoe red unlocktal Nil have "expr_locks e l > 0"
	    by -(rule red_unlock_no_wait_expr_locks)
	  ultimately show ?thesis by simp
	next
	  case (Suspend w)
	  note ta = red_suspend_conv[OF red Suspend]
	  with L tal have "w = l" by(simp split: split_if_asm)
	  with ta have tal': "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock, ReleaseAcquire]" by simp
	  with tal L have "xs = []"
	    by(auto simp add: append_eq_Cons_conv Cons_eq_append_conv)
	  with nhl have nhl: "\<not> has_lock (ls l) t" by(simp)
	  with tst ex lockok have "expr_locks e l = 0"
	    by(auto dest: lock_okD2)
	  with tal' have "\<exists>e' s'. P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" using red
	    by -(rule red_Unlock_Lock_no_lock_ex_UnlockFail, auto)
	  then obtain e' s'
	    where red': "P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" by blast
	  obtain m' x' where s': "s' = (m', x')" by (cases s', auto)
	  with red' ex nhl show ?thesis
	    by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def
                        elim!: collect_locks'E split: if_splits)
	next
	  case (Notify w)
	  note ta = red_notify_conv[OF red Notify]
	  with red tal L have w: "w = l"
	    by(simp split: split_if_asm)
	  with ta have tal': "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]" by simp
	  with tal L have xs: "xs = []"
	    by(auto simp add: append_eq_Cons_conv Cons_eq_append_conv)
	  with nhl have nhl: "\<not> has_lock (ls l) t" by simp
	  from red tal' have "\<exists>e' s'. P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
	    by - (erule red_Unlock_Lock_no_lock_ex_UnlockFail, simp)
	  then obtain e' s'
	    where red': "P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" by blast
	  obtain m' x' where s': "s' = (m', x')" by (cases s', auto)
	  with red' ex nhl show ?thesis
	    by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def
                        elim!: collect_locks'E split: if_splits)
	next
	  case (NotifyAll w)
	  note ta = red_notifyAll_conv[OF red NotifyAll]
	  with red tal L have w: "w = l"
	    by(simp split: split_if_asm)
	  with ta have tal': "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]" by simp
	  with tal L have xs: "xs = []"
	    by(auto simp add: append_eq_Cons_conv Cons_eq_append_conv)
	  with nhl have nhl: "\<not> has_lock (ls l) t" by simp
	  from red tal' have "\<exists>e' s'. P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>"
	    by - (erule red_Unlock_Lock_no_lock_ex_UnlockFail, simp)
	  then obtain e' s'
	    where red': "P \<turnstile> \<langle>e, (m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', s'\<rangle>" by blast
	  obtain m' x' where s': "s' = (m', x')" by (cases s', auto)
	  with red' ex nhl show ?thesis
	    by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def
                        elim!: collect_locks'E split: if_splits)
	qed
      next
	case UnlockFail
	note L = `L = UnlockFail`
	note hl = `has_lock (upd_locks (ls l) t xs) t`
	from L red tal aoe have tal': "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
	  by -(erule red_UnlockFail_UnlockFail, auto)
	from L tal tal' have xs: "xs = []" and ys: "ys = []"
	  by(auto simp add: append_eq_Cons_conv Cons_eq_append_conv)
	with hl have hl: "has_lock (ls l) t" by simp
	hence laoul: "lock_actions_ok (ls l) t [Unlock, Lock]"
	  by(auto intro: may_lock_t_may_lock_unlock_lock_t has_lock_may_lock)
	hence "lock_ok_las' ls t ((\<lambda>l. [])(l := [Unlock, Lock]))"
	  and "lock_ok_las' ls t ((\<lambda>l. [])(l := [Unlock, Lock, ReleaseAcquire]))"
	  by(auto simp add: lock_ok_las'_def lock_actions_ok'_def)
	moreover from red_UnlockFail_ex_Unlock[OF red tal']
	obtain e' s'
	  where "P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l, ReleaseAcquire\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Suspend l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>Notify l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>
              \<or> P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>\<lbrace>\<^bsub>w\<^esub>NotifyAll l\<rbrace>\<rightarrow> \<langle>e',s'\<rangle>" by blast
	moreover have "collect_locks' ((\<lambda>l. [])(l := [Unlock, Lock, ReleaseAcquire])) \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
	  by(auto intro: collect_locksI elim!: collect_locks'E split: split_if_asm)
	moreover have "collect_locks' ((\<lambda>l. [])(l := [Unlock, Lock])) \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
	  by(auto intro: collect_locksI elim!: collect_locks'E split: split_if_asm)
	ultimately show ?thesis using ex
	  by(cases s') fastsimp
      qed
    qed
  next
    case False
    then obtain xs TA ys
      where tat: "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys"
      and tok: "thread_oks ts m' xs"
      and ntok: "\<not> thread_ok (redT_updTs ts xs) m' TA"
      by(auto simp add: not_thread_oks_conv)
    from tat red obtain t where tat': "(\<exists>e x. ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread t (e, x) m'\<rbrace>) \<or> ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists t \<rbrace>"
      by(fastsimp dest!: red_thread_at_most_one simp add: Cons_eq_append_conv)
    with tat have xs: "xs = []" 
      and ys: "ys = []"
      by(auto simp add: append_eq_Cons_conv Cons_eq_append_conv)
    with ntok have ntok: "\<not> thread_ok ts m' TA" by(simp)
    from tat' show ?thesis
    proof(rule disjE)
      assume "\<exists>e x. ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread t (e, x) m'\<rbrace>"
      then obtain e'' x''
	where tat': "ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread t (e'', x'') m'\<rbrace>"
	by blast
      with tat xs ys have TA: "TA = NewThread t (e'', x'') m'" by(simp)
      with ntok have "\<not> free_thread_id ts t" by(simp)
      moreover from red_NewThread_NewThreadFail[OF red] tat' obtain e' m' x'
	where red': "P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists t \<rbrace>\<rightarrow> \<langle>e',(m', x')\<rangle>" by fastsimp
      ultimately show ?thesis using ex
	by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def elim: collect_locks'E)
    next
      assume tat': "ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists t \<rbrace>"
      with tat xs ys have TA: "TA = ThreadExists t" by(simp)
      with ntok have t: "free_thread_id ts t" by(auto)
      moreover from red_NewThreadFail_NewThread[OF red] tat'
      obtain e' l' h' e'' x'' where "P \<turnstile> \<langle>e,(m, x)\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread t (e'', x'') h'\<rbrace>\<rightarrow> \<langle>e',(h', l')\<rangle>"
	by(fastsimp)
      ultimately show ?thesis using ex
	by(fastsimp simp add: lock_ok_las'_def lock_actions_ok'_def elim: collect_locks'E)
    qed
  qed
  with s show "\<exists>ta' x' m'. mred P (ex, shr s) ta' (x', m') \<and>
             thread_oks (thr s) m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and>
             lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and>
             collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
             red_mthr.cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and>
             red_mthr.collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> red_mthr.collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    by simp
qed


lemma wf_progress: 
  assumes wf: "wf_J_prog P"
  and "sconf_type_ts_ok P Es (thr S) (shr S)"
  and "def_ass_ts_ok (thr S) (shr S)"
  shows "wf_progress final_expr (mred P) S"
proof(unfold_locales)
  fix tta s t ex ln
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s"
    and "thr s t = \<lfloor>(ex, ln)\<rfloor>"
    and "\<not> final_expr ex"
  moreover obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s) auto
  moreover obtain e x where ex: "ex = (e, x)" by(cases ex) auto
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
    using nfine by(auto dest!: red_progress[OF wwf])
  thus "\<exists>ta x' m'. mred P (ex, shr s) ta (x', m')" using ex s
    by(fastsimp)
qed

lemma progress_deadlock: 
  assumes wf: "wf_J_prog P"
  and "sync_es_ok (thr s) (shr s)"
  and "sconf_type_ts_ok P Es (thr s) (shr s)"
  and "def_ass_ts_ok (thr s) (shr s)"
  and "lock_ok (locks s) (thr s)"
  shows "progress final_expr (mred P) s (final_thread_wf.deadlock final_expr (mred P))"
using assms
apply -
apply(rule final_thread_wf.progress_deadlock)
   apply(rule final_thread_wf_interp)
  apply(rule wf_progress, assumption+)
 apply(rule red_wf_red, assumption+)
by(rule preserves_lock_thread_ok)

lemma progress_deadlocked': 
  assumes wf: "wf_J_prog P"
  and "sync_es_ok (thr s) (shr s)"
  and "sconf_type_ts_ok P Es (thr s) (shr s)"
  and "def_ass_ts_ok (thr s) (shr s)"
  and "lock_ok (locks s) (thr s)"
  shows "progress final_expr (mred P) s (final_thread_wf.deadlocked' final_expr (mred P))"
using assms
apply -
apply(rule final_thread_wf.progress_deadlocked')
   apply(rule final_thread_wf_interp)
  apply(rule wf_progress, assumption+)
 apply(rule red_wf_red, assumption+)
by(rule preserves_lock_thread_ok)

lemma redT_progress_deadlocked:
  "\<lbrakk> wf_J_prog P; sync_es_ok (thr start_state) (shr start_state);
     sconf_type_ts_ok P Es (thr start_state) (shr start_state);
     def_ass_ts_ok (thr start_state) (shr start_state); lock_ok (locks start_state) (thr start_state);
     P \<turnstile> start_state -\<triangleright>?ttas\<rightarrow>* s; red_mthr_final.not_final_thread s t;
     \<not> red_mthr_final.deadlocked P s t\<rbrakk>
  \<Longrightarrow> \<exists>t' ta' s'. P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
by(rule progress.redT_progress[OF progress_deadlocked' _ _ final_thread_wf.not_deadlocked'I[OF final_thread_wf_interp]])

lemma redT_pregress_deadlock:
  "\<lbrakk> wf_J_prog P; sync_es_ok (thr start_state) (shr start_state);
     sconf_type_ts_ok P Es (thr start_state) (shr start_state);
     def_ass_ts_ok (thr start_state) (shr start_state); lock_ok (locks start_state) (thr start_state);
     P \<turnstile> start_state -\<triangleright>?ttas\<rightarrow>* s;
     red_mthr_final.not_final_thread s t; \<not> red_mthr_final.deadlock P s\<rbrakk>
  \<Longrightarrow> \<exists>t' ta' s'. P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
by(rule progress.redT_progress[OF progress_deadlock])

corollary TypeSafetyT:
  fixes ttas :: "(thread_id \<times> (addr,thread_id,expr \<times> locals,heap,addr) thread_action) list"
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
                  \<or> red_mthr_final.deadlocked P s' t \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,shr s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)))
          \<and> Es \<unlhd> Es')"
proof(rule conjI)
  from RedT tc show "thread_conf P (thr s') (shr s')" by(rule RedT_preserves_thread_conf)
next
  let ?Es' = "upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) ttas\<down>)"
  obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by(cases s) auto
  obtain ls' ts' m' ws' where s' [simp]: "s' = (ls', (ts', m'), ws')" by(cases s') auto
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
	then obtain l where "ln' l > 0"
	  by(auto simp add: neq_no_wait_locks_conv)
	from lock' es't have "has_locks (ls' l) t + ln' l = expr_locks e' l"
	  by(auto dest: lock_okD2)
	with `ln' l > 0` have "expr_locks e' l > 0" by simp
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
      with es't have "red_mthr_final.not_final_thread s' t"
	by(auto intro: red_mthr_final.not_final_thread.intros)
      with nored have "red_mthr_final.deadlocked P s' t"
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
      ultimately have "red_mthr_final.deadlocked P s' t \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T))" .. }
    ultimately have "(\<exists>v. e' = Val v \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,m' \<turnstile> v :\<le> T) \<and> ln' = no_wait_locks)
                   \<or> (\<exists>a. e' = Throw a \<and> a \<in> dom m' \<and> ln' = no_wait_locks)
                   \<or> red_mthr_final.deadlocked P s' t \<and> (\<exists>E T. ?Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T))"
      by(blast) }
  moreover
  have "Es \<unlhd> ?Es'" using esinv RedT
    by (auto intro: multithreaded.RedT_upd_inv_ext)
  ultimately show "let Es' = upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) ttas\<down>) in
          (\<forall>t e'. \<exists>x' ln'. thr s' t = \<lfloor>((e', x'), ln')\<rfloor> \<longrightarrow>
                    (\<exists>v. e' = Val v \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,shr s' \<turnstile> v :\<le> T) \<and> ln' = no_wait_locks)
                  \<or> (\<exists>a. e' = Throw a \<and> a \<in> dom (shr s') \<and> ln' = no_wait_locks)
                  \<or> red_mthr_final.deadlocked P s' t \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,shr s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)))
          \<and> Es \<unlhd> Es'" by(simp)
qed

end

