(*  Title:      JinjaThreads/Common/ExternalCallWF.thy
    Author:     Andreas Lochbihler
*)

header{* \isaheader{ Properties of external calls in well-formed programs } *}

theory ExternalCallWF imports WellForm Conform "../Framework/FWSemantics" begin

lemma WT_red_external_list_imp_red_external:
  "\<lbrakk> (ta, va, h') \<in> set (red_external_list P a M vs h); P,h \<turnstile> a\<bullet>M(vs) : U \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
apply(fastsimp elim!: external_WT.cases external_WT'.cases simp add: red_external_list_def simp del: ta_update_locks.simps ta_update_NewThread.simps ta_update_Conditional.simps ta_update_wait_set.simps split: heapobj.split_asm intro: red_external.intros)
done

lemma WT_red_external_list_conv:
  "P,h \<turnstile> a\<bullet>M(vs) : U \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<longleftrightarrow> (ta, va, h') \<in> set (red_external_list P a M vs h)"
by(blast intro: WT_red_external_list_imp_red_external red_external_imp_red_external_list elim: external_WT'.cases)


primrec conf_extRet :: "'m prog \<Rightarrow> heap \<Rightarrow> val + addr \<Rightarrow> ty \<Rightarrow> bool" where
  "conf_extRet P h (Inl v) T = (P,h \<turnstile> v :\<le> T)"
| "conf_extRet P h (Inr a) T = (P,h \<turnstile> Addr a :\<le> Class Throwable)"


lemma external_call_hconf:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; P,h \<turnstile> a\<bullet>M(vs) : U; P \<turnstile> h \<surd> \<rbrakk>
  \<Longrightarrow> P \<turnstile> h' \<surd>"
by(auto elim: red_external.cases)


lemma red_external_conf_extRet:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; P,h \<turnstile> a\<bullet>M(vs) : U; preallocated h \<rbrakk>
  \<Longrightarrow> conf_extRet P h' va U"
apply(auto elim!: red_external.cases external_WT.cases external_WT'.cases)
apply(auto simp del: typeof_h.simps simp add: typeof_IllegalMonitorState conf_def intro: xcpt_subcls_Throwable)
done

lemma red_external_new_thread_addr_conf:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; NewThread t (C, M, a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; h a \<noteq> None \<rbrakk>
  \<Longrightarrow> P,h' \<turnstile> Addr a :\<le> Class Thread"
by(auto elim!: red_external.cases simp add: conf_def split: heapobj.split_asm)


lemma red_external_new_thread_sees:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; h a \<noteq> None \<rbrakk>
  \<Longrightarrow> (\<exists>fs. h' a' = \<lfloor>Obj C fs\<rfloor>) \<and> (\<exists>T meth D. P \<turnstile> C sees M':[]\<rightarrow>T = meth in D)"
by(fastsimp elim!: red_external.cases split: heapobj.split_asm simp add: widen_Class dest: sub_Thread_sees_run)

lemma red_external_new_thread_sub_thread:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; h a \<noteq> None \<rbrakk>
  \<Longrightarrow> (\<exists>fs. h' a' = \<lfloor>Obj C fs\<rfloor>) \<and> P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M' = run"
by(auto elim!: red_external.cases split: heapobj.split_asm simp add: widen_Class dest: sub_Thread_sees_run)

lemma red_external_wf_red:
  assumes red: "P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  obtains ta' va' h''
  where "P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta'\<rightarrow>ext \<langle>va', h''\<rangle>" "final_thread.actions_ok' s t ta'" "final_thread.actions_subset ta' ta"
proof(atomize_elim)
  show "\<exists>ta' va' h'. P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta'\<rightarrow>ext \<langle>va', h'\<rangle> \<and> final_thread.actions_ok' s t ta' \<and> final_thread.actions_subset ta' ta"
  proof(cases "final_thread.actions_ok' s t ta")
    case True
    have "final_thread.actions_subset ta ta" by(rule final_thread.actions_subset_refl)
    with True red show ?thesis by blast
  next
    case False
    note [simp] = final_thread.actions_ok'_iff lock_ok_las'_def final_thread.cond_action_oks'_iff
      final_thread.actions_subset_iff
    note [rule del] = subsetI
    note [intro] = collect_locks'_subset_collect_locks red_external.intros
    
    from red show ?thesis
    proof cases
      case (RedNewThread C)
      note ta = `ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a (C, run, a) h\<rbrace>\<lbrace>\<^bsub>o\<^esub>ThreadStart a\<rbrace>`
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists a\<rbrace>"
      from ta False have "final_thread.actions_ok' s t ?ta'" by(auto)
      moreover from ta have "final_thread.actions_subset ?ta' ta" by auto
      ultimately show ?thesis using RedNewThread by(fastsimp)
    next
      case RedNewThreadFail
      then obtain va' h' x where "P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a x h'\<rbrace>\<lbrace>\<^bsub>o\<^esub>ThreadStart a\<rbrace>\<rightarrow>ext \<langle>va', h'\<rangle>" by(fastsimp)
      moreover from `ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists a\<rbrace>` False
      have "final_thread.actions_ok' s t \<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a x h'\<rbrace>\<lbrace>\<^bsub>o\<^esub>ThreadStart a\<rbrace>" by(auto)
      moreover from `ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists a\<rbrace>`
      have "final_thread.actions_subset \<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a x h'\<rbrace>\<lbrace>\<^bsub>o\<^esub>ThreadStart a\<rbrace> ta" by(auto)
      ultimately show ?thesis by blast
    next
      case RedJoin thus ?thesis by fastsimp
    next
      case RedWait
      note ta = `ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>`
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
      from ta False have "\<not> may_lock ((locks s)\<^sub>f a) t \<or> \<not> has_lock ((locks s)\<^sub>f a) t"
	by(auto simp add: lock_actions_ok'_iff finfun_upd_apply split: split_if_asm dest: may_lock_t_may_lock_unlock_lock_t)
      hence "\<not> has_lock ((locks s)\<^sub>f a) t" by(metis has_lock_may_lock)
      hence "final_thread.actions_ok' s t ?ta'" by(auto simp add: lock_actions_ok'_iff finfun_upd_apply)
      moreover from ta have "final_thread.actions_subset ?ta' ta"
	by(auto simp add: collect_locks'_def finfun_upd_apply)
      moreover from RedWait obtain va h' where "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
      ultimately show ?thesis by blast
    next
      case RedWaitFail
      note ta = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>`
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>"
      from ta False have "has_lock ((locks s)\<^sub>f a) t" by(auto simp add: finfun_upd_apply split: split_if_asm)
      hence "final_thread.actions_ok' s t ?ta'" by(auto simp add: finfun_upd_apply intro: has_lock_may_lock)
      moreover from ta have "final_thread.actions_subset ?ta' ta"
	by(auto simp add: collect_locks'_def finfun_upd_apply)
      moreover from RedWaitFail obtain va h' where "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
      ultimately show ?thesis by blast
    next
      case RedNotify
      note ta = `ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub>Notify a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>`
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
      from ta False have "\<not> may_lock ((locks s)\<^sub>f a) t \<or> \<not> has_lock ((locks s)\<^sub>f a) t"
	by(auto simp add: lock_actions_ok'_iff finfun_upd_apply split: split_if_asm dest: may_lock_t_may_lock_unlock_lock_t)
      hence "\<not> has_lock ((locks s)\<^sub>f a) t" by(metis has_lock_may_lock)
      hence "final_thread.actions_ok' s t ?ta'" by(auto simp add: lock_actions_ok'_iff finfun_upd_apply)
      moreover from ta have "final_thread.actions_subset ?ta' ta"
	by(auto simp add: collect_locks'_def finfun_upd_apply)
      moreover from RedNotify obtain va h' where "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
      ultimately show ?thesis by blast
    next
      case RedNotifyFail
      note ta = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>`
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub>Notify a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>"
      from ta False have "has_lock ((locks s)\<^sub>f a) t" by(auto simp add: finfun_upd_apply split: split_if_asm)
      hence "final_thread.actions_ok' s t ?ta'" by(auto simp add: finfun_upd_apply intro: has_lock_may_lock)
      moreover from ta have "final_thread.actions_subset ?ta' ta"
	by(auto simp add: collect_locks'_def finfun_upd_apply)
      moreover from RedNotifyFail obtain va h' where "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
      ultimately show ?thesis by blast
    next
      case RedNotifyAll
      note ta = `ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub>NotifyAll a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>`
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
      from ta False have "\<not> may_lock ((locks s)\<^sub>f a) t \<or> \<not> has_lock ((locks s)\<^sub>f a) t"
	by(auto simp add: lock_actions_ok'_iff finfun_upd_apply split: split_if_asm dest: may_lock_t_may_lock_unlock_lock_t)
      hence "\<not> has_lock ((locks s)\<^sub>f a) t" by(metis has_lock_may_lock)
      hence "final_thread.actions_ok' s t ?ta'" by(auto simp add: lock_actions_ok'_iff finfun_upd_apply)
      moreover from ta have "final_thread.actions_subset ?ta' ta"
	by(auto simp add: collect_locks'_def finfun_upd_apply)
      moreover from RedNotifyAll obtain va h' where "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
      ultimately show ?thesis by blast
    next
      case RedNotifyAllFail
      note ta = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>`
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub>NotifyAll a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a\<rbrace>"
      from ta False have "has_lock ((locks s)\<^sub>f a) t" by(auto simp add: finfun_upd_apply split: split_if_asm)
      hence "final_thread.actions_ok' s t ?ta'" by(auto simp add: finfun_upd_apply intro: has_lock_may_lock)
      moreover from ta have "final_thread.actions_subset ?ta' ta"
	by(auto simp add: collect_locks'_def finfun_upd_apply)
      moreover from RedNotifyAllFail obtain va h' where "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
      ultimately show ?thesis by blast
    qed
  qed
qed

end