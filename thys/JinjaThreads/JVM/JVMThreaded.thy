(*  Title:      JinjaThreads/JVM/JVMDefensive.thy
    Author:     Andreas Lochbihler
*)

header{* \isaheader{Instantiating the framework semantics with the JVM} *}

theory JVMThreaded imports "../Framework/FWSemantics" JVMDefensive "../Common/ConformThreaded" begin

primrec JVM_final :: "jvm_thread_state \<Rightarrow> bool"
where
  "JVM_final (xcp, frs) = (frs = [])"


text{* The aggressive JVM *}

abbreviation
  mexec :: "jvm_prog \<Rightarrow> (jvm_thread_state \<times> heap) \<Rightarrow> jvm_thread_action \<Rightarrow> (jvm_thread_state \<times> heap) \<Rightarrow> bool"
where
  "mexec P \<equiv> (\<lambda>((xcp, frstls), h) ta  ((xcp', frstls'), h'). P \<turnstile> (xcp, h, frstls) -ta-jvm\<rightarrow> (xcp', h', frstls'))"

lemma NewThread_memory_exec_instr:
  "\<lbrakk> (ta, s) \<in> set (exec_instr I P h stk loc C M pc frs); NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m = fst (snd s)"
apply(cases I)
apply(auto split: split_if_asm simp add: split_beta)
apply(auto dest!: red_ext_list_new_thread_heap simp add: extRet2JVM_def[folded Datatype.sum_case_def] split: sum.split)
done

lemma NewThread_memory_exec:
  "\<lbrakk> P \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m = (fst (snd \<sigma>'))"
apply(erule exec_1.cases)
apply(clarsimp)
apply(case_tac bb, simp)
apply(case_tac af, auto simp add: exception_step_def_raw split: list.split_asm)
apply(drule NewThread_memory_exec_instr, simp+)
done

lemma exec_mthr: "multithreaded (mexec P)"
apply(unfold_locales)
apply(clarsimp)
apply(drule NewThread_memory_exec, fastsimp)
apply(simp)
done

interpretation exec_mthr: multithreaded JVM_final "mexec P"
by(rule exec_mthr)

abbreviation
  mexecT :: "jvm_prog
             \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
             \<Rightarrow> thread_id \<times> (addr,thread_id,jvm_thread_state,heap,addr,(addr,obs_event) observable) thread_action
             \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
where
  "mexecT P \<equiv> exec_mthr.redT P"

abbreviation
  mexecT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                  \<Rightarrow> thread_id \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr,(addr,obs_event) observable) thread_action
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow>\<^bsub>jvm\<^esub> _" [50,0,0,0,50] 80)
where
  "mexecT_syntax1 P s t ta s' \<equiv> mexecT P s (t, ta) s'"


abbreviation
  mExecT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                  \<Rightarrow> (thread_id \<times> (addr,thread_id,jvm_thread_state,heap,addr,(addr,obs_event) observable) thread_action) list
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>\<^bsub>jvm\<^esub>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s' \<equiv> exec_mthr.RedT P s ttas s'"


text{* The defensive JVM *}

abbreviation
  mexecd :: "jvm_prog \<Rightarrow> jvm_thread_state \<times> heap \<Rightarrow> jvm_thread_action \<Rightarrow> jvm_thread_state \<times> heap \<Rightarrow> bool"
where
  "mexecd P \<equiv> (\<lambda>((xcp, frstls), h) ta ((xcp', frstls'), h'). P \<turnstile> Normal (xcp, h, frstls) -ta-jvmd\<rightarrow> Normal (xcp', h', frstls'))"


lemma execd_mthr: "multithreaded (mexecd P)"
apply(unfold_locales, auto)
apply(erule jvmd_NormalE)
apply(clarsimp)
apply(case_tac xcp, auto simp add: exception_step_def_raw split: list.split_asm)
apply(drule NewThread_memory_exec_instr, simp+)
done

interpretation execd_mthr: multithreaded JVM_final "mexecd P"
by(rule execd_mthr)

abbreviation
  mexecdT :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                       \<Rightarrow> thread_id \<times> (addr,thread_id,jvm_thread_state,heap,addr,(addr,obs_event) observable) thread_action
                       \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
where
  "mexecdT P \<equiv> execd_mthr.redT P"


abbreviation
  mexecdT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                  \<Rightarrow> thread_id \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr,(addr,obs_event) observable) thread_action
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow>\<^bsub>jvmd\<^esub> _" [50,0,0,0,50] 80)
where
  "mexecdT_syntax1 P s t ta s' \<equiv> mexecdT P s (t, ta) s'"


abbreviation
  mExecdT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                  \<Rightarrow> (thread_id \<times> (addr,thread_id,jvm_thread_state,heap,addr,(addr,obs_event) observable) thread_action) list
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>\<^bsub>jvmd\<^esub>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s' \<equiv> execd_mthr.RedT P s ttas s'"


lemma execd_hext:
  "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s' \<Longrightarrow> hext (shr s) (shr s')"
apply(erule execd_mthr.redT.cases)
 apply(clarsimp)
 apply(frule jvmd_NormalD)
apply(auto dest: exec_1_d_hext)
done

end
