(*  Title:      JinjaThreads/Framework/FWProgressAux.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Auxiliary definitions for the progress theorem for the multithreaded semantics} *}

theory FWProgressAux imports FWSemantics begin

context multithreaded begin

definition must_sync :: "'x \<Rightarrow> 'm \<Rightarrow> bool" ("\<langle>_,/ _\<rangle>/ \<wrong>" [0,0] 81) where
  "must_sync x m = ((\<forall>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<longrightarrow> (\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)) \<and>
                    (\<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>))"

lemma must_syncI:
  "\<lbrakk> \<And>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<Longrightarrow> (\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>);
     \<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<rbrakk>
  \<Longrightarrow> \<langle>x, m\<rangle> \<wrong>"
by(fastsimp simp add: must_sync_def)

lemma must_syncE:
  "\<lbrakk> \<langle>x, m\<rangle> \<wrong>; 
     \<And>ta x' m'. \<lbrakk> \<forall>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<longrightarrow> (\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>); 
                  \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<rbrakk> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
by(auto simp only: must_sync_def)


lemma must_syncD:
  "\<lbrakk> \<langle>x, m\<rangle> \<wrong>; \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<rbrakk> \<Longrightarrow> (\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
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


end


locale final_thread_wf = multithreaded +
  constrains final :: "'x \<Rightarrow> bool"
  constrains r :: "('l,'t,'x,'m,'w) semantics"
  assumes final_no_red [dest]: "\<lbrakk> final x; r (x, m) ta (x', m') \<rbrakk> \<Longrightarrow> False" begin

lemma final_no_redT: 
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<rbrakk> \<Longrightarrow> \<not> final x"
by(auto elim!: redT_elims dest: final_no_red)

definition final_thread :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool" where
  "final_thread s t \<equiv> (case thr s t of None \<Rightarrow> False | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> final x \<and> ln = no_wait_locks \<and> wset s t = None)"

lemma final_threadI:
  "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; final x; wset s t = None \<rbrakk> \<Longrightarrow> final_thread s t"
by(simp add: final_thread_def)

lemma final_threadE:
  assumes "final_thread s t"
  obtains x where "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "final x" "wset s t = None"
using assms by(auto simp add: final_thread_def)

inductive not_final_thread :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool"
for s :: "('l,'t,'x,'m,'w) state" and t :: "'t" where
  not_final_thread_final: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> final x \<rbrakk> \<Longrightarrow> not_final_thread s t"
| not_final_thread_wait_locks: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ln \<noteq> no_wait_locks \<rbrakk> \<Longrightarrow> not_final_thread s t"
| not_final_thread_wait_set: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> not_final_thread s t"

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

lemma not_final_thread_existsE:
  assumes "not_final_thread s t"
  obtains x ln where "thr s t = \<lfloor>(x, ln)\<rfloor>"
using assms by blast

lemma not_final_thread_final_thread_conv:
  "thr s t \<noteq> None \<Longrightarrow> \<not> final_thread s t \<longleftrightarrow> not_final_thread s t"
by(simp add: not_final_thread_iff final_thread_def)


lemma may_join_cond_action_oks:
  assumes "\<And>t. Join t \<in> set cas \<Longrightarrow> \<not> not_final_thread s t"
  shows "cond_action_oks s t cas"
proof -
  have "\<forall>t. Join t \<in> set cas \<longrightarrow> \<not> not_final_thread s t \<Longrightarrow> cond_action_oks s t cas"
  proof(induct cas)
    case Nil thus ?case by(clarsimp)
  next
    case (Cons CA CAS)
    thus ?case by(cases CA, auto simp add: not_final_thread_iff)
  qed
  with assms show ?thesis by blast
qed

end

end