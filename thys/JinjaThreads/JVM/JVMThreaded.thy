(*  Title:      JinjaThreads/JVM/JVMDefensive.thy
    Author:     Andreas Lochbihler
*)

header{* \isaheader{Instantiating the framework semantics with the JVM} *}

theory JVMThreaded imports
  JVMDefensive
  "../Common/ConformThreaded"
  "../Framework/FWLiftingSem"
begin

primrec JVM_final :: "jvm_thread_state \<Rightarrow> bool"
where
  "JVM_final (xcp, frs) = (frs = [])"

text{* The aggressive JVM *}

context JVM_heap_base begin

abbreviation
  mexec :: "jvm_prog \<Rightarrow> thread_id \<Rightarrow> (jvm_thread_state \<times> 'heap) \<Rightarrow> 'heap jvm_thread_action \<Rightarrow> (jvm_thread_state \<times> 'heap) \<Rightarrow> bool"
where
  "mexec P t \<equiv> (\<lambda>((xcp, frstls), h) ta ((xcp', frstls'), h'). P,t \<turnstile> (xcp, h, frstls) -ta-jvm\<rightarrow> (xcp', h', frstls'))"

lemma NewThread_memory_exec_instr:
  "\<lbrakk> (ta, s) \<in> exec_instr I P t h stk loc C M pc frs; NewThread t' x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m = fst (snd s)"
apply(cases I)
apply(auto split: split_if_asm simp add: split_beta ta_upd_simps)
apply(auto dest!: red_ext_aggr_new_thread_heap simp add: extRet2JVM_def split: extCallRet.split)
done

lemma NewThread_memory_exec:
  "\<lbrakk> P,t \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'; NewThread t' x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m = (fst (snd \<sigma>'))"
apply(erule exec_1.cases)
apply(clarsimp)
apply(case_tac bb, simp)
apply(case_tac af, auto simp add: exception_step_def_raw split: list.split_asm)
apply(drule NewThread_memory_exec_instr, simp+)
done

lemma exec_instr_Suspend_last:
  "(ta, s) \<in> exec_instr I P t h stk loc C M pc frs \<Longrightarrow> Suspend w \<notin> set (butlast \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>)"
apply(cases I)
apply(auto split: split_if_asm simp add: split_beta ta_upd_simps)
apply(auto dest!: red_external_aggr_Suspend_last)
done

lemma mexec_Suspend_last:
  "P,t \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>' \<Longrightarrow> Suspend w \<notin> set (butlast \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>)"
apply(erule exec_1.cases)
apply(clarsimp)
apply(case_tac bb, simp)
apply(case_tac af, auto simp add: exception_step_def_raw split: list.split_asm)
apply(drule exec_instr_Suspend_last)
apply auto
done


lemma exec_mthr: "multithreaded (mexec P)"
apply(unfold_locales)
apply(clarsimp, drule NewThread_memory_exec, fastsimp, simp)
apply(clarsimp, drule mexec_Suspend_last, fastsimp)
done

end

sublocale JVM_heap_base < exec_mthr!: 
  multithreaded
    JVM_final
    "mexec P"
  for P
by(rule exec_mthr)

context JVM_heap_base begin

abbreviation
  mexecT :: "jvm_prog
             \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state
             \<Rightarrow> thread_id \<times> (jvm_thread_state,'heap) JT_thread_action
             \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state \<Rightarrow> bool"
where
  "mexecT P \<equiv> exec_mthr.redT P"

abbreviation
  mexecT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state
                  \<Rightarrow> thread_id \<Rightarrow> (jvm_thread_state,'heap) JT_thread_action
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow>\<^bsub>jvm\<^esub> _" [50,0,0,0,50] 80)
where
  "mexecT_syntax1 P s t ta s' \<equiv> mexecT P s (t, ta) s'"


abbreviation
  mExecT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state
                  \<Rightarrow> (thread_id \<times> (jvm_thread_state,'heap) JT_thread_action) list
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>\<^bsub>jvm\<^esub>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s' \<equiv> exec_mthr.RedT P s ttas s'"


text{* The defensive JVM *}

abbreviation
  mexecd :: "jvm_prog \<Rightarrow> thread_id \<Rightarrow> jvm_thread_state \<times> 'heap \<Rightarrow> 'heap jvm_thread_action \<Rightarrow> jvm_thread_state \<times> 'heap \<Rightarrow> bool"
where
  "mexecd P t \<equiv> (\<lambda>((xcp, frstls), h) ta ((xcp', frstls'), h'). P,t \<turnstile> Normal (xcp, h, frstls) -ta-jvmd\<rightarrow> Normal (xcp', h', frstls'))"


lemma execd_mthr: "multithreaded (mexecd P)"
apply(unfold_locales, auto)
 apply(erule jvmd_NormalE)
 apply(clarsimp)
 apply(case_tac xcp, auto simp add: exception_step_def_raw split: list.split_asm)[1]
 apply(drule NewThread_memory_exec_instr, simp, simp)
apply(erule jvmd_NormalE)
apply clarsimp
apply(case_tac xcp, auto)
apply(drule exec_instr_Suspend_last)
apply fastsimp
done

end

sublocale JVM_heap_base < execd_mthr!:
  multithreaded
    JVM_final
    "mexecd P"
  for P
by(rule execd_mthr)

context JVM_heap_base begin

abbreviation
  mexecdT :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state
                       \<Rightarrow> thread_id \<times> (jvm_thread_state,'heap) JT_thread_action
                       \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state \<Rightarrow> bool"
where
  "mexecdT P \<equiv> execd_mthr.redT P"


abbreviation
  mexecdT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state
                  \<Rightarrow> thread_id \<Rightarrow> (jvm_thread_state,'heap) JT_thread_action
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow>\<^bsub>jvmd\<^esub> _" [50,0,0,0,50] 80)
where
  "mexecdT_syntax1 P s t ta s' \<equiv> mexecdT P s (t, ta) s'"


abbreviation
  mExecdT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state
                  \<Rightarrow> (thread_id \<times> (jvm_thread_state,'heap) JT_thread_action) list
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>\<^bsub>jvmd\<^esub>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s' \<equiv> execd_mthr.RedT P s ttas s'"


lemma exec_instr_New_Thread_exists_thread_object:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr ins P t h stk loc C M pc frs;
     check_instr ins P h stk loc C M pc frs;
     NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' t' = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(cases ins)
apply(fastsimp simp add: split_beta ta_upd_simps split: split_if_asm intro: red_external_aggr_new_thread_exists_thread_object)+
done

lemma exec_New_Thread_exists_thread_object:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' t' = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(cases xcp)
apply(case_tac [!] frs)
apply(auto simp add: check_def elim!: jvmd_NormalE dest!: exec_instr_New_Thread_exists_thread_object)
done

end

context JVM_heap begin

lemma exec_instr_preserve_tconf:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr ins P t h stk loc C M pc frs;
     check_instr ins P h stk loc C M pc frs;
     P,h \<turnstile> t' \<surd>t \<rbrakk>
  \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
apply(cases ins)
apply(auto intro: tconf_hext_mono hext_heap_ops_mono' hext_heap_write split: split_if_asm simp add: split_beta intro: red_external_aggr_preserves_tconf)
done

lemma exec_preserve_tconf:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); P,h \<turnstile> t' \<surd>t \<rbrakk> \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
apply(cases xcp)
apply(case_tac [!] frs)
apply(auto simp add: check_def elim!: jvmd_NormalE elim!: exec_instr_preserve_tconf)
done

lemma lifting_wf_thread_conf: "lifting_wf (mexecd P) (\<lambda>t x m. P,m \<turnstile> t \<surd>t)"
by(unfold_locales)(auto intro: exec_preserve_tconf dest: exec_New_Thread_exists_thread_object intro: tconfI)

end

sublocale JVM_heap < execd_tconf!: lifting_wf JVM_final "mexecd P" "\<lambda>t x m. P,m \<turnstile> t \<surd>t" for P
by(rule lifting_wf_thread_conf)

context JVM_heap begin

lemma redTW_hext_d:
  "execd_mthr.redTW P t wa s obs s' \<Longrightarrow> shr s \<unlhd> shr s'"
by(fastsimp elim!: execd_mthr.redTW.cases dest: ts_okD tconfD intro: exec_1_d_hext)

lemma redTWs_hext_d:
  assumes "execd_mthr.redTWs P t wa s obs s'"
  shows "shr s \<unlhd> shr s'"
using assms
by(induct rule: execd_mthr.redTWs_converse_induct)(auto dest: redTW_hext_d execd_tconf.redTWs_preserves intro: hext_trans)

lemma execd_hext:
  "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s' \<Longrightarrow> shr s \<unlhd> shr s'"
by(auto elim!: execd_mthr.redT.cases dest!: exec_1_d_hext redTWs_hext_d intro: hext_trans)

lemma Execd_hext:
  assumes "P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  shows "shr s \<unlhd> shr s'"
using assms unfolding execd_mthr.RedT_def
by(induct)(auto dest!: execd_hext intro: hext_trans simp add: execd_mthr.RedT_def)

end

end
