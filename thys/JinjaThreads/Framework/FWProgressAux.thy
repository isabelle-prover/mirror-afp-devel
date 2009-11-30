(*  Title:      JinjaThreads/Framework/FWProgressAux.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Auxiliary definitions for the progress theorem for the multithreaded semantics} *}

theory FWProgressAux imports FWSemantics begin

context multithreaded_base begin

definition must_sync :: "'x \<Rightarrow> 'm \<Rightarrow> bool" ("\<langle>_,/ _\<rangle>/ \<wrong>" [0,0] 81) where
  "must_sync x m = (\<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>)"

lemma must_syncI:
  "\<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<Longrightarrow> \<langle>x, m\<rangle> \<wrong>"
by(fastsimp simp add: must_sync_def)

lemma must_syncE:
  "\<lbrakk> \<langle>x, m\<rangle> \<wrong>; \<And>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto simp only: must_sync_def)


definition can_sync :: "'x \<Rightarrow> 'm \<Rightarrow> ('l + 't) set \<Rightarrow> bool" ("\<langle>_,/ _\<rangle>/ _/ \<wrong>" [0,0,0] 81) where
  "\<langle>x, m\<rangle> LT \<wrong> \<equiv> \<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> (LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>})"

lemma can_syncI:
  "\<lbrakk> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} \<rbrakk> \<Longrightarrow> \<langle>x, m\<rangle> LT \<wrong>"
by(cases ta)(fastsimp simp add: can_sync_def)

lemma can_syncE:
  assumes "\<langle>x, m\<rangle> LT \<wrong>"
  obtains ta x' m'
  where "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>" "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
  using assms
by(clarsimp simp add: can_sync_def)

lemma must_sync_ex_can_sync:
  "\<langle>x, m\<rangle> \<wrong> \<Longrightarrow> \<exists>LT. \<langle>x, m\<rangle> LT \<wrong>"
by(auto intro: can_syncI elim!: must_syncE)

lemma can_sync_must_sync:
  "\<langle>x, m\<rangle> LT \<wrong> \<Longrightarrow> \<langle>x, m\<rangle> \<wrong>"
by(auto intro: must_syncI elim!: can_syncE)

lemma must_sync_can_sync_conv:
  "\<langle>x, m\<rangle> \<wrong> \<longleftrightarrow> (\<exists>LT. \<langle>x, m\<rangle> LT \<wrong>)"
by(auto intro: must_sync_ex_can_sync can_sync_must_sync)


end

text {* Well-formedness conditions for final *}

context final_thread begin

definition final_thread :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool" where
  "final_thread s t \<equiv> (case thr s t of None \<Rightarrow> False | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> final x \<and> ln = no_wait_locks \<and> wset s t = None)"

inductive not_final_thread :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool"
for s :: "('l,'t,'x,'m,'w) state" and t :: "'t" where
  not_final_thread_final: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> final x \<rbrakk> \<Longrightarrow> not_final_thread s t"
| not_final_thread_wait_locks: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ln \<noteq> no_wait_locks \<rbrakk> \<Longrightarrow> not_final_thread s t"
| not_final_thread_wait_set: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> not_final_thread s t"

lemma final_threadI:
  "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; final x; wset s t = None \<rbrakk> \<Longrightarrow> final_thread s t"
by(simp add: final_thread_def)

lemma final_threadE:
  assumes "final_thread s t"
  obtains x where "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "final x" "wset s t = None"
using assms by(auto simp add: final_thread_def)

declare not_final_thread.cases [elim]

lemmas not_final_thread_cases = not_final_thread.cases [consumes 1, case_names final wait_locks wait_set]

lemma not_final_thread_cases2 [consumes 2, case_names final wait_locks wait_set]:
  "\<lbrakk> not_final_thread s t; thr s t = \<lfloor>(x, ln)\<rfloor>;
     \<not> final x \<Longrightarrow> thesis; ln \<noteq> no_wait_locks \<Longrightarrow> thesis; \<And>w. wset s t = \<lfloor>w\<rfloor> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
by(auto)

lemma not_final_thread_iff:
  "not_final_thread s t \<longleftrightarrow> (\<exists>x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<not> final x \<or> ln \<noteq> no_wait_locks \<or> (\<exists>w. wset s t = \<lfloor>w\<rfloor>)))"
by(auto intro: not_final_thread.intros)

lemma not_final_thread_conv:
  "not_final_thread s t \<longleftrightarrow> thr s t \<noteq> None \<and> \<not> final_thread s t"
by(auto simp add: final_thread_def intro: not_final_thread.intros)

lemma not_final_thread_existsE:
  assumes "not_final_thread s t"
  obtains x ln where "thr s t = \<lfloor>(x, ln)\<rfloor>"
using assms by blast

lemma not_final_thread_final_thread_conv:
  "thr s t \<noteq> None \<Longrightarrow> \<not> final_thread s t \<longleftrightarrow> not_final_thread s t"
by(simp add: not_final_thread_iff final_thread_def)

lemma may_join_cond_action_oks:
  assumes "\<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'"
  shows "cond_action_oks s t cas"
using assms
proof (induct cas)
  case Nil thus ?case by clarsimp
next
  case (Cons ca cas)
  note IH = `(\<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t') \<Longrightarrow> cond_action_oks s t cas`
  note ass = `\<And>t'. Join t' \<in> set (ca # cas) \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'`
  hence "\<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'" by simp
  hence "cond_action_oks s t cas" by(rule IH)
  moreover have "cond_action_ok s t ca"
  proof(cases ca)
    case (Join t')
    with ass have "\<not> not_final_thread s t'" "t \<noteq> t'" by auto
    thus ?thesis using Join by(auto simp add: not_final_thread_iff)
  qed
  ultimately show ?case by simp
qed

end

locale final_thread_wf = multithreaded _ r
  for r :: "('l,'t,'x,'m,'w,'o) semantics" +
  assumes final_no_red [dest]: "\<lbrakk> final x; r (x, m) ta (x', m') \<rbrakk> \<Longrightarrow> False" begin

lemma final_no_redT: 
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<rbrakk> \<Longrightarrow> \<not> final x"
by(auto elim!: redT_elims dest: final_no_red)

lemma red_not_final_thread:
  "s -t\<triangleright>ta\<rightarrow> s' \<Longrightarrow> not_final_thread s t"
by(fastsimp elim: redT.cases intro: not_final_thread.intros)

lemma redT_preserves_final_thread:
  "\<lbrakk> s -t'\<triangleright>ta\<rightarrow> s'; final_thread s t \<rbrakk> \<Longrightarrow> final_thread s' t"
apply(erule redT.cases)
apply(auto simp add: final_thread_def dest: redT_updTs_None redT_updTs_Some intro: redT_updWs_None_implies_None)
done

end

end