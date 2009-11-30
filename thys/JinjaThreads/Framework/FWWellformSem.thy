(*  Title:      JinjaThreads/Framework/FWWellformSem.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Wellformedness properties for the instantiating semantics and the multithreaded state } *}

theory FWWellformSem imports FWProgressAux begin

text {* This locale simply fixes a start state *}
locale multithreaded_start = multithreaded _ r
  for r :: "('l,'t,'x,'m,'w,'o) semantics" +
  fixes start_state :: "('l,'t,'x,'m,'w) state"
  assumes lock_thread_ok_start_state: "lock_thread_ok (locks start_state) (thr start_state)"
begin

lemma preserves_lock_thread_ok: 
  "start_state -\<triangleright>tta\<rightarrow>* s \<Longrightarrow> lock_thread_ok (locks s) (thr s)"
  by(erule RedT_preserves_lock_thread_ok[OF _ lock_thread_ok_start_state])

end


locale wf_red = multithreaded_start _ r start_state
  for r :: "('l,'t,'x,'m,'w,'o) semantics" and start_state :: "('l,'t,'x,'m,'w) state" +
  assumes wf_red:
    "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
       r (x, shr s) ta (x', m') \<rbrakk>
     \<Longrightarrow> \<exists>ta' x' m'. r (x, shr s) ta' (x', m') \<and> final_thread.actions_ok' s t ta' \<and> final_thread.actions_subset ta' ta"
begin

lemmas wf_red_refl = wf_red[OF RedT_refl]


lemma wf_redE:
  assumes "start_state -\<triangleright>ttas\<rightarrow>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "\<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>"
  obtains ta' x' m'
  where "\<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>" "actions_ok' s t ta'" "actions_subset ta' ta"
using assms
by(blast dest: wf_red)

lemma wf_redE':
  assumes "start_state -\<triangleright>ttas\<rightarrow>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "\<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>"
  obtains ta' x' m'
  where "\<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>" "thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>"
  and "lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>" "collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  and "cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>"
  and "collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
using assms
by(blast dest: wf_red)

end


locale preserve_lock_behav = multithreaded_start _ r
  for r :: "('l,'t,'x,'m,'w,'o) semantics" +
  assumes can_lock_preserved: 
    "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; s -t'\<triangleright>ta'\<rightarrow> s';
       thr s t = \<lfloor>(x, ln)\<rfloor>; \<langle>x, shr s\<rangle> L \<wrong>; L \<noteq> {} \<rbrakk>
    \<Longrightarrow> \<langle>x, shr s'\<rangle> \<wrong>"
  and can_lock_devreserp:
    "\<lbrakk> RedT start_state tta s; s -t'\<triangleright>ta'\<rightarrow> s';
       thr s t = \<lfloor>(x, ln)\<rfloor>; \<langle>x, shr s'\<rangle> L \<wrong> \<rbrakk>
    \<Longrightarrow> \<exists>L'\<subseteq>L. \<langle>x, shr s\<rangle> L' \<wrong>"

locale wf_progress = final_thread final + multithreaded_start final r start_state 
  for final :: "'x \<Rightarrow> bool" and r :: "('l,'t,'x,'m,'w,'o) semantics" and start_state :: "('l,'t,'x,'m,'w) state" +
  assumes wf_progress: "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> final x \<rbrakk>
                        \<Longrightarrow> \<exists>ta x' m'. \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
begin

lemmas wf_progress_refl = wf_progress[OF RedT_refl]

lemma wf_progressE:
  assumes "start_state -\<triangleright>tta\<rightarrow>* s"
  and "thr s t = \<lfloor>(x, ln)\<rfloor>" "\<not> final x"
  obtains ta x' m' where "\<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
using assms
by(blast dest: wf_progress)

lemmas wf_progress_reflE = wf_progressE[OF RedT_refl]

end


end