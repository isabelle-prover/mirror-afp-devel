(*  Title:      JinjaThreads/Framework/FWWellformSem.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Wellformedness properties for the instantiating semantics and the multithreaded state } *}

theory FWWellformSem imports FWProgressAux begin

text {* This locale simple fixes a start state *}
locale multithreaded_start = multithreaded _ r
  for r :: "('l,'t,'x,'m,'w) semantics" +
(*  constrains final :: "'x \<Rightarrow> bool"
  constrains r :: "('l,'t,'x,'m,'w) semantics" *)
  fixes start_state :: "('l,'t,'x,'m,'w) state"

locale wf_red = multithreaded_start +
  assumes wf_red:
    "\<lbrakk> multithreaded.RedT final r start_state tta s; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
       r (x, shr s) ta (x', m') \<rbrakk>
     \<Longrightarrow> \<exists>ta' x' m'. r (x, shr s) ta' (x', m') \<and> thread_oks (thr s) m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and>
                    lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and>
                    collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
                    final_thread.cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and>
                    final_thread.collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> final_thread.collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
begin

lemmas wf_red_refl = wf_red[OF RedT_refl]

lemma wf_redE:
  assumes "start_state -\<triangleright>ttas\<rightarrow>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "\<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>"
  obtains ta' x' m'
  where "\<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>" "thread_oks (thr s) m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>"
  and "lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>" "collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  and "cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>"
  and "collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
using assms
by(blast dest: wf_red)

end


locale preserve_lock_behav = multithreaded_start _ r
  for r :: "('l,'t,'x,'m,'w) semantics" +
  assumes must_lock_preserved: 
    "\<lbrakk> multithreaded.RedT final r start_state tta s; multithreaded.redT final r s (t', ta') s';
       thr s t = \<lfloor>(x, ln)\<rfloor>; multithreaded.must_sync r x (shr s) \<rbrakk>
    \<Longrightarrow> multithreaded.must_sync r x (shr s')"
  and can_lock_devreserp:
    "\<lbrakk> multithreaded.RedT final r start_state tta s; multithreaded.redT final r s (t', ta') s';
       thr s t = \<lfloor>(x, ln)\<rfloor>; multithreaded.can_sync r x (shr s') L; L \<noteq> {} \<rbrakk>
    \<Longrightarrow> \<exists>L'\<subseteq>L. multithreaded.can_sync r x (shr s) L'"



locale wf_progress = final_thread + multithreaded_start +
  assumes wf_progress: "\<lbrakk> multithreaded.RedT final r start_state tta s; thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> final x \<rbrakk>
                        \<Longrightarrow> \<exists>ta x' m'. r (x, shr s) ta (x', m')"
begin

lemmas wf_progress_refl = wf_progress[OF RedT_refl]

lemma wf_progressE:
  assumes "multithreaded.RedT final r start_state tta s"
  and "thr s t = \<lfloor>(x, ln)\<rfloor>" "\<not> final x"
  obtains ta x' m' where "\<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
using assms
by(blast dest: wf_progress)

lemmas wf_progress_reflE = wf_progressE[OF RedT_refl]

end


locale preserves_lock_thread_ok = multithreaded_start +
  assumes lock_thread_ok: "multithreaded.RedT final r start_state ttas s \<Longrightarrow> lock_thread_ok (locks s) (thr s)"

end