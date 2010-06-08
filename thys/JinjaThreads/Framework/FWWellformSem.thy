(*  Title:      JinjaThreads/Framework/FWWellformSem.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Wellformedness properties for the instantiating semantics and the multithreaded state } *}

theory FWWellformSem imports FWProgressAux begin

locale wf_red = multithreaded_start final r start_state
  for final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80)
  and start_state :: "('l,'t,'x,'m,'w) state" +
  assumes wf_red:
  "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; wset s t = None;
     t \<turnstile> (x, shr s) -ta\<rightarrow> (x', m') \<rbrakk>
  \<Longrightarrow> \<exists>ta' x' m'. t \<turnstile> (x, shr s) -ta'\<rightarrow> (x', m') \<and> actions_ok' s t ta' \<and> actions_subset ta' ta"
  
  and wf_red_wait:
  "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = \<lfloor>w\<rfloor>;
     thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>; wset s t' = None;
     t' \<turnstile> \<langle>x', shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>;
     interrupted_mem_reds (thr s) (wset s) m'' m''' \<rbrakk>
  \<Longrightarrow> (\<exists>x'. t \<turnstile> (x, m''') -\<epsilon>\<lbrace>\<^bsub>c\<^esub>Notified\<rbrace>\<rightarrow> (x', m''')) \<and> (\<exists>x' ta m. t \<turnstile> (x, m''') -ta\<rightarrow> (x', m) \<and> is_Interrupted_ta ta)"

begin

lemma wf_redE:
  assumes "start_state -\<triangleright>ttas\<rightarrow>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>" "wset s t = None"
  obtains ta' x' m'
  where "t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>" "actions_ok' s t ta'" "actions_subset ta' ta"
using assms
by(blast dest: wf_red)

lemma wf_redE':
  assumes "start_state -\<triangleright>ttas\<rightarrow>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>" "wset s t = None"
  obtains ta' x' m'
  where "t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>" "thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>"
  and "lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>" "collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  and "cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>"
  and "collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
using assms
by(blast dest: wf_red)

end

locale wf_progress = final_thread final + multithreaded_start final r start_state 
  for final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80)
  and start_state :: "('l,'t,'x,'m,'w) state" +
  assumes wf_progress: "\<lbrakk> start_state -\<triangleright>tta\<rightarrow>* s; thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> final x \<rbrakk>
                        \<Longrightarrow> \<exists>ta x' m'. t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
begin

lemmas wf_progress_refl = wf_progress[OF RedT_refl]

lemma wf_progressE:
  assumes "start_state -\<triangleright>tta\<rightarrow>* s"
  and "thr s t = \<lfloor>(x, ln)\<rfloor>" "\<not> final x"
  obtains ta x' m' where "t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
using assms
by(blast dest: wf_progress)

lemmas wf_progress_reflE = wf_progressE[OF RedT_refl]

end


end