(*  Title:      JinjaThreads/JVM/JVMDefensive.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

theory JVMThreaded imports "../Framework/FWSemantics" JVMDefensive "../Common/ConformThreaded" begin

fun final :: "jvm_thread_state \<Rightarrow> bool"
where
  "final (xcp, frs) = (frs = [])"


(* agressive JVM *)

abbreviation
  mexec :: "jvm_prog \<Rightarrow> (jvm_thread_state \<times> heap) \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action \<Rightarrow> (jvm_thread_state \<times> heap) \<Rightarrow> bool"
where
  "mexec P \<equiv> (\<lambda>((xcp, frstls), h) ta  ((xcp', frstls'), h'). P \<turnstile> (xcp, h, frstls) -ta-jvm\<rightarrow> (xcp', h', frstls'))"

interpretation exec_mthr!: multithreaded final "mexec P" .

abbreviation
  mexecT :: "jvm_prog
             \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
             \<Rightarrow> thread_id \<times> (addr,thread_id,jvm_thread_state,heap,addr) thread_action
             \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
where
  "mexecT P \<equiv> exec_mthr.redT P"

abbreviation
  mexecT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                  \<Rightarrow> thread_id \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow>\<^bsub>jvm\<^esub> _" [50,0,0,0,50] 80)
where
  "mexecT_syntax1 P s t ta s' \<equiv> mexecT P s (t, ta) s'"


abbreviation
  mExecT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                  \<Rightarrow> (thread_id \<times> (addr,thread_id,jvm_thread_state,heap,addr) thread_action) list
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>\<^bsub>jvm\<^esub>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s' \<equiv> exec_mthr.RedT P s ttas s'"


(* defensive JVM *)

abbreviation
  mexecd :: "jvm_prog \<Rightarrow> jvm_thread_state \<times> heap \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action \<Rightarrow> jvm_thread_state \<times> heap \<Rightarrow> bool"
where
  "mexecd P \<equiv> (\<lambda>((xcp, frstls), h) ta ((xcp', frstls'), h'). P \<turnstile> Normal (xcp, h, frstls) -ta-jvmd\<rightarrow> Normal (xcp', h', frstls'))"

interpretation execd_mthr!: multithreaded final "mexecd P" .

abbreviation
  mexecdT :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                       \<Rightarrow> thread_id \<times> (addr,thread_id,jvm_thread_state,heap,addr) thread_action
                       \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
where
  "mexecdT P \<equiv> execd_mthr.redT P"


abbreviation
  mexecdT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                  \<Rightarrow> thread_id \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow>\<^bsub>jvmd\<^esub> _" [50,0,0,0,50] 80)
where
  "mexecdT_syntax1 P s t ta s' \<equiv> mexecdT P s (t, ta) s'"


abbreviation
  mExecdT_syntax1 :: "jvm_prog \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state
                  \<Rightarrow> (thread_id \<times> (addr,thread_id,jvm_thread_state,heap,addr) thread_action) list
                  \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>\<^bsub>jvmd\<^esub>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s' \<equiv> execd_mthr.RedT P s ttas s'"


lemma execd_hext:
  "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s' \<Longrightarrow> hext (shr s) (shr s')"
apply(erule multithreaded.redT.cases)
 apply(clarsimp)
 apply(frule jvmd_NormalD)
apply(auto dest: exec_1_d_hext)
done

end
