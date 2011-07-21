(*  Title:      JinjaThreads/Common/ExternalCall.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of method calls that cannot be defined inside JinjaThreads} *}

theory ExternalCall imports
  "../Framework/FWSemantics"
  "Conform"
begin

type_synonym
  ('addr,'thread_id,'heap) external_thread_action = "('addr, 'thread_id, cname \<times> mname \<times> 'addr,'heap) Jinja_thread_action"

(* pretty printing for external_thread_action type *)
print_translation {*
  let
    fun tr'
       [a1, t
       , Const (@{type_syntax "prod"}, _) $ Const (@{type_syntax "String.literal"}, _) $
           (Const (@{type_syntax "prod"}, _) $ Const (@{type_syntax "String.literal"}, _) $ a2)
       , h] =
      if a1 = a2 then Syntax.const @{type_syntax "external_thread_action"} $ a1 $ t $ h
      else raise Match;
    in [(@{type_syntax "Jinja_thread_action"}, tr')]
  end
*}
typ "('addr,'thread_id,'heap) external_thread_action"

subsection {* Typing of external calls *}

inductive external_WT_defs :: "ty \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> bool" ("(_\<bullet>_'(_')) :: _" [50, 0, 0, 50] 60)
where
  "Class Thread\<bullet>start([]) :: Void"
| "Class Thread\<bullet>join([]) :: Void"
| "Class Thread\<bullet>interrupt([]) :: Void"
| "Class Thread\<bullet>isInterrupted([]) :: Boolean"
| "Class Object\<bullet>wait([]) :: Void"
| "Class Object\<bullet>notify([]) :: Void"
| "Class Object\<bullet>notifyAll([]) :: Void"
| "Class Object\<bullet>clone([]) :: Class Object"
| "Class Object\<bullet>hashcode([]) :: Integer"
| "Class Object\<bullet>print([Integer]) :: Void"
| "Class Object\<bullet>currentThread([]) :: Class Thread"
| "Class Object\<bullet>interrupted([]) :: Boolean"
| "Class Object\<bullet>yield([]) :: Void"

definition native_call :: 
  "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" 
  ("_ \<turnstile> _ native _:_\<rightarrow>_ in _" [51,51,51,51,51,51] 50)
where
  "P \<turnstile> T native M:Ts\<rightarrow>Tr in T' \<longleftrightarrow>
  (P \<turnstile> T \<le> T' \<and> T \<noteq> NT \<and> T'\<bullet>M(Ts) :: Tr \<and>
   (\<forall>C Ts Tr body D. is_class_type_of T C \<longrightarrow> P \<turnstile> C sees M:Ts\<rightarrow>Tr=body in D \<longrightarrow> P \<turnstile> T' \<le> Class D \<and> T' \<noteq> Class D))"

inductive external_WT :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> (_\<bullet>_'(_')) :: _" [50, 0, 0, 50] 60)
where
  "P \<turnstile> T native M:Ts\<rightarrow>U in T' \<Longrightarrow> P \<turnstile> T\<bullet>M(Ts) :: U"

inductive (in heap_base) external_WT' :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> ty \<Rightarrow> bool"
  ("_,_ \<turnstile> (_\<bullet>_'(_')) : _" [50,0,0,0,50] 60)
for P :: "'m prog" and h :: 'heap and a :: 'addr and M :: mname and vs :: "'addr val list" and U :: ty
where "\<lbrakk> typeof_addr h a = \<lfloor>T\<rfloor>; map typeof\<^bsub>h\<^esub> vs = map Some Ts; P \<turnstile> T\<bullet>M(Ts') :: U; P \<turnstile> Ts [\<le>] Ts' \<rbrakk> \<Longrightarrow> P,h \<turnstile> a\<bullet>M(vs) : U"

inductive is_native :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> bool"
for P and T and M
where "P \<turnstile> T native M:Ts\<rightarrow>Tr in T' \<Longrightarrow> is_native P T M"

inductive_cases external_WT_defs_cases:
  "a\<bullet>start(vs) :: T"
  "a\<bullet>join(vs) :: T"
  "a\<bullet>interrupt(vs) :: T"
  "a\<bullet>isInterrupted(vs) :: T"
  "a\<bullet>wait(vs) :: T"
  "a\<bullet>notify(vs) :: T"
  "a\<bullet>notifyAll(vs) :: T"
  "a\<bullet>clone(vs) :: T"
  "a\<bullet>hashcode(vs) :: T"
  "a\<bullet>print(vs) :: T"
  "a\<bullet>currentThread(vs) :: T"
  "a\<bullet>interrupted([]) :: T"
  "a\<bullet>yield(vs) :: T"

lemma native_callI:
  "\<lbrakk> P \<turnstile> T \<le> T'; T'\<bullet>M(Ts) :: Tr; T \<noteq> NT;
     \<And>C Ts Tr body D. \<lbrakk> is_class_type_of T C; P \<turnstile> C sees M:Ts\<rightarrow>Tr=body in D \<rbrakk> \<Longrightarrow> P \<turnstile> T' \<le> Class D \<and> T' \<noteq> Class D \<rbrakk>
  \<Longrightarrow> P \<turnstile> T native M:Ts\<rightarrow>Tr in T'"
unfolding native_call_def by blast

lemma is_native_def2:
  "is_native P T M \<longleftrightarrow> (\<exists>Ts Tr T'. P \<turnstile> T native M:Ts\<rightarrow>Tr in T')"
by(rule is_native.simps)

lemma native_call_not_NT:
  "P \<turnstile> T native M:Ts\<rightarrow>Tr in T' \<Longrightarrow> T \<noteq> NT"
by(simp add: native_call_def)

lemma native_call_not_NT':
  "P \<turnstile> T native M:Ts\<rightarrow>Tr in T' \<Longrightarrow> T' \<noteq> NT"
by(auto simp add: native_call_def)

lemma native_call_sees_method:
  "\<lbrakk> P \<turnstile> T native M:Ts\<rightarrow>Tr in T'; P \<turnstile> C sees M: Ts' \<rightarrow> Tr' = mthd in D; is_class_type_of T C \<rbrakk>
  \<Longrightarrow> P \<turnstile> T' \<le> Class D"
by(auto simp add: native_call_def)

lemma native_call_fun:
  "\<lbrakk> P \<turnstile> T native M:Ts\<rightarrow>Tr in T'; P \<turnstile> T native M:Ts'\<rightarrow>Tr' in T'' \<rbrakk>
  \<Longrightarrow> Ts = Ts' \<and> Tr = Tr' \<and> T' = T''"
by(auto simp add: native_call_def elim!: external_WT_defs.cases)

lemma external_WT_determ:
  "\<lbrakk> P \<turnstile> T\<bullet>M(Ts) :: U; P \<turnstile> T\<bullet>M(Ts') :: U' \<rbrakk> \<Longrightarrow> Ts = Ts' \<and> U = U'"
by(auto elim!: external_WT.cases dest: native_call_fun)

lemma external_WT_The_conv:
  "P \<turnstile> T\<bullet>M(TS) :: U \<Longrightarrow> (THE U. P \<turnstile> T\<bullet>M(TS) :: U) = U"
by(auto dest: external_WT_determ)

lemma external_WT_The_Ex_conv:
  "P \<turnstile> T\<bullet>M(TS) :: U \<Longrightarrow> (THE U. \<exists>TS. P \<turnstile> T\<bullet>M(TS) :: U) = U"
by(auto dest: external_WT_determ)

lemma external_WT_The_Ex_conv2:
  "\<lbrakk> P \<turnstile> T\<bullet>M(Ts') :: U; P \<turnstile> Ts [\<le>] Ts' \<rbrakk> \<Longrightarrow> (THE U. \<exists>Ts'. P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T\<bullet>M(Ts') :: U) = U"
by(auto dest: external_WT_determ)

lemma external_WT_is_native:
  "P \<turnstile> T\<bullet>M(Ts) :: U \<Longrightarrow> is_native P T M"
by(auto elim!: external_WT.cases simp add: is_native_def2)

lemma external_WT_not_NT:
  "P \<turnstile> T\<bullet>M(Ts) :: U \<Longrightarrow> T \<noteq> NT"
by(auto elim!: external_WT.cases dest: native_call_not_NT)

lemma external_WT_defs_is_refT:
  "T\<bullet>M(Ts) :: Tr \<Longrightarrow> is_refT T"
by(auto elim: external_WT_defs.cases)

lemma native_native_overriding:
  assumes "P \<turnstile> T native M:Ts\<rightarrow>Tr in T'"
  and "P \<turnstile> U native M:Us\<rightarrow>Ur in U'"
  and "P \<turnstile> U \<le> T"
  shows "P \<turnstile> Ts [\<le>] Us" "P \<turnstile> Ur \<le> Tr"
using assms
by(auto simp add: native_call_def widen_Class elim!: external_WT_defs.cases)

lemma native_call_is_refT: "P \<turnstile> T native M:Ts\<rightarrow>Tr in T' \<Longrightarrow> is_refT T"
by(auto simp add: native_call_def dest: external_WT_defs_is_refT intro: widen_refT)

lemma is_native_is_refT: "is_native P T M \<Longrightarrow> is_refT T"
by(auto simp add: is_native_def2 intro: native_call_is_refT)

lemma is_native_not_NT: "is_native P T M \<Longrightarrow> T \<noteq> NT"
by(auto simp add: is_native_def2 dest: native_call_not_NT)

lemma not_is_native_NT [simp]: "\<not> is_native P NT M"
by(blast dest: is_native_not_NT)

context heap_base begin

lemma external_WT'_iff:
  "P,h \<turnstile> a\<bullet>M(vs) : U \<longleftrightarrow> 
  (\<exists>T Ts Ts'. typeof_addr h a = \<lfloor>T\<rfloor> \<and> map typeof\<^bsub>h\<^esub> vs = map Some Ts \<and> P \<turnstile> T\<bullet>M(Ts') :: U \<and> P \<turnstile> Ts [\<le>] Ts')"
by(auto simp add: external_WT'_def lfp_const)

end

context heap begin

lemma external_WT'_hext_mono:
  "\<lbrakk> P,h \<turnstile> a\<bullet>M(vs) : T; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> a\<bullet>M(vs) : T"
by(auto simp add: external_WT'_iff dest: typeof_addr_hext_mono map_typeof_hext_mono)

end

subsection {* Semantics of external calls *}

datatype 'addr extCallRet = 
    RetVal "'addr val"
  | RetExc 'addr
  | RetStaySame

lemma extCallRet_rec [simp]: "extCallRet_rec = extCallRet_case"
by(auto simp add: fun_eq_iff split: extCallRet.split)

context heap_base begin

abbreviation RetEXC :: "cname \<Rightarrow> 'addr extCallRet"
where "RetEXC C \<equiv> RetExc (addr_of_sys_xcpt C)"

inductive heap_copy_loc :: "'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'heap \<Rightarrow> ('addr, 'thread_id) obs_event list \<Rightarrow> 'heap \<Rightarrow> bool"
for a :: 'addr and a' :: 'addr and al :: addr_loc and h :: 'heap
where
  "\<lbrakk> heap_read h a al v; heap_write h a' al v h' \<rbrakk>
  \<Longrightarrow> heap_copy_loc a a' al h ([ReadMem a al v, WriteMem a' al v]) h'"

inductive heap_copies :: "'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc list \<Rightarrow> 'heap \<Rightarrow> ('addr, 'thread_id) obs_event list \<Rightarrow> 'heap \<Rightarrow> bool"
for a :: 'addr and a' :: 'addr
where
  Nil: "heap_copies a a' [] h [] h"
| Cons:
  "\<lbrakk> heap_copy_loc a a' al h ob h'; heap_copies a a' als h' obs h'' \<rbrakk>
  \<Longrightarrow> heap_copies a a' (al # als) h (ob @ obs) h''"

inductive_cases heap_copies_cases:
  "heap_copies a a' [] h ops h'"
  "heap_copies a a' (al#als) h ops h'"

text {*
  Contrary to Sun's JVM 1.6.0\_07, cloning an interrupted thread does not yield an interrupted thread,
  because the interrupt flag is not stored inside the thread object.
  Starting a clone of a started thread with Sun JVM 1.6.0\_07 raises an illegal thread state exception,
  we just start another thread.
  The thread at \texttt{http://mail.openjdk.java.net/pipermail/core-libs-dev/2010-August/004715.html} discusses 
  the general problem of thread cloning and argues against that.
  The bug report \texttt{http://bugs.sun.com/bugdatabase/view\_bug.do?bug\_id=6968584} 
  changes the Thread class implementation
  such that \texttt{Object.clone()} can no longer be accessed for Thread and subclasses in Java 7.

  Array cells are never volatile themselves.
  *}

inductive heap_clone :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> 'heap \<Rightarrow> (('addr, 'thread_id) obs_event list \<times> 'addr) option \<Rightarrow> bool"
for P :: "'m prog" and h :: 'heap and a :: 'addr 
where
  ObjFail:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; new_obj h C = (h', None) \<rbrakk>
  \<Longrightarrow> heap_clone P h a h' None"
| ArrFail:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array T\<rfloor>; new_arr h T (array_length h a) = (h', None) \<rbrakk>
  \<Longrightarrow> heap_clone P h a h' None"
| ObjClone:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; new_obj h C = (h', \<lfloor>a'\<rfloor>);
     P \<turnstile> C has_fields FDTs; heap_copies a a' (map (\<lambda>((F, D), Tfm). CField D F) FDTs) h' obs h'' \<rbrakk>
  \<Longrightarrow> heap_clone P h a h'' \<lfloor>(NewObj a' C # obs, a')\<rfloor>"
| ArrClone:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array T\<rfloor>; n = array_length h a; new_arr h T n = (h', \<lfloor>a'\<rfloor>); P \<turnstile> Object has_fields FDTs;
     heap_copies a a' (map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]) h' obs  h'' \<rbrakk>
  \<Longrightarrow> heap_clone P h a h'' \<lfloor>(NewArr a' T n # obs, a')\<rfloor>"

inductive red_external ::
  "'m prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list 
  \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr extCallRet \<Rightarrow> 'heap \<Rightarrow> bool"
  and red_external_syntax :: 
  "'m prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> 'heap 
  \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr extCallRet \<Rightarrow> 'heap \<Rightarrow> bool"
  ("_,_ \<turnstile> (\<langle>(_\<bullet>_'(_')),/_\<rangle>) -_\<rightarrow>ext (\<langle>(_),/(_)\<rangle>)" [50, 0, 0, 0, 0, 0, 0, 0, 0] 51)
for P :: "'m prog" and t :: 'thread_id and h :: 'heap and a :: 'addr
where
  "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<equiv> red_external P t h a M vs ta va h'"

| RedNewThread:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>start([]), h\<rangle> -\<lbrace>NewThread (addr2thread_id a) (C, run, a) h, ThreadStart (addr2thread_id a) \<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNewThreadFail:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>start([]), h\<rangle> -\<lbrace>ThreadExists (addr2thread_id a) True\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalThreadState, h\<rangle>"

| RedJoin:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>join([]), h\<rangle> -\<lbrace>Join (addr2thread_id a), IsInterrupted t False, ThreadJoin (addr2thread_id a)\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedJoinInterrupt:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>join([]), h\<rangle> -\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>\<rightarrow>ext \<langle>RetEXC InterruptedException, h\<rangle>"

    -- {* 
    Interruption should produce inter-thread actions (JLS 17.4.4) for the synchronizes-with order.
    They should synchronize with the inter-thread actions that determine whether a thread has been interrupted.
    Hence, interruption generates an @{term "ObsInterrupt"} action.

    Although @{term WakeUp} causes the interrupted thread to raise an @{term InterruptedException}
    independent of the interrupt status, the interrupt flag must be set with @{term "Interrupt"} 
    such that other threads observe the interrupted thread as interrupted
    while it competes for the monitor lock again.

    Interrupting a thread which has not yet been started does not set the interrupt flag 
    (tested with Sun HotSpot JVM 1.6.0\_07).
    *}
  
| RedInterrupt:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>interrupt([]), h\<rangle> 
            -\<lbrace>ThreadExists (addr2thread_id a) True, WakeUp (addr2thread_id a), 
              Interrupt (addr2thread_id a), ObsInterrupt (addr2thread_id a)\<rbrace>\<rightarrow>ext
            \<langle>RetVal Unit, h\<rangle>"

| RedInterruptInexist:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>interrupt([]), h\<rangle> 
            -\<lbrace>ThreadExists (addr2thread_id a) False\<rbrace>\<rightarrow>ext
            \<langle>RetVal Unit, h\<rangle>"

| RedIsInterruptedTrue:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>isInterrupted([]), h\<rangle> -\<lbrace> IsInterrupted (addr2thread_id a) True, ObsInterrupted (addr2thread_id a)\<rbrace>\<rightarrow>ext
           \<langle>RetVal (Bool True), h\<rangle>"

| RedIsInterruptedFalse:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>isInterrupted([]), h\<rangle> -\<lbrace>IsInterrupted (addr2thread_id a) False\<rbrace>\<rightarrow>ext \<langle>RetVal (Bool False), h\<rangle>"

    -- {*
    The JLS leaves unspecified whether @{term wait} first checks for the monitor state
    (whether the thread holds a lock on the monitor) or for the interrupt flag of the current thread.
    Sun Hotspot JVM 1.6.0\_07 seems to check for the monitor state first, so we do it here, too.
    *}
| RedWaitInterrupt:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace> \<rightarrow>ext 
         \<langle>RetEXC InterruptedException, h\<rangle>"

| RedWait:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>Suspend a, Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a \<rbrace>\<rightarrow>ext 
         \<langle>RetStaySame, h\<rangle>"

| RedWaitFail:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>UnlockFail\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedWaitNotified:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>Notified\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

    -- {*
    This rule does NOT check that the interrupted flag is set, but still clears it.
    The semantics will be that only the executing thread clears its interrupt.
    *}
| RedWaitInterrupted:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>WokenUp, ClearInterrupt t, ObsInterrupted t\<rbrace>\<rightarrow>ext \<langle>RetEXC InterruptedException, h\<rangle>"

    -- {*
    @{term notify} and @{term notifyAll} do not perform synchronization inter-thread actions
    because they only tests whether the thread holds a lock, but do not change the lock state.
    *}

| RedNotify:
  "P,t \<turnstile> \<langle>a\<bullet>notify([]), h\<rangle> -\<lbrace>Notify a, Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNotifyFail:
  "P,t \<turnstile> \<langle>a\<bullet>notify([]), h\<rangle> -\<lbrace>UnlockFail\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedNotifyAll:
  "P,t \<turnstile> \<langle>a\<bullet>notifyAll([]), h\<rangle> -\<lbrace>NotifyAll a, Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNotifyAllFail:
  "P,t \<turnstile> \<langle>a\<bullet>notifyAll([]), h\<rangle> -\<lbrace>UnlockFail\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedClone:
  "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor> 
    \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>clone([]), h\<rangle> -(\<lambda>\<^isup>f [], [], [], [], [], obs)\<rightarrow>ext \<langle>RetVal (Addr a'), h'\<rangle>"

| RedCloneFail:
  "heap_clone P h a h' None \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>clone([]), h\<rangle> -\<epsilon>\<rightarrow>ext \<langle>RetEXC OutOfMemory, h'\<rangle>"

| RedHashcode:
  "P,t \<turnstile> \<langle>a\<bullet>hashcode([]), h\<rangle> -\<lbrace>\<rbrace>\<rightarrow>ext \<langle>RetVal (Intg (word_of_int (hash_addr a))), h\<rangle>"

| RedPrint:
  "P,t \<turnstile> \<langle>a\<bullet>print(vs), h\<rangle> -\<lbrace>ExternalCall a print vs Unit\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedCurrentThread:
  "P,t \<turnstile> \<langle>a\<bullet>currentThread([]), h\<rangle> -\<lbrace>\<rbrace>\<rightarrow>ext \<langle>RetVal (Addr (thread_id2addr t)), h\<rangle>"

| RedInterruptedTrue:
  "P,t \<turnstile> \<langle>a\<bullet>interrupted([]), h\<rangle> -\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>\<rightarrow>ext \<langle>RetVal (Bool True), h\<rangle>"

| RedInterruptedFalse:
  "P,t \<turnstile> \<langle>a\<bullet>interrupted([]), h\<rangle> -\<lbrace>IsInterrupted t False\<rbrace>\<rightarrow>ext \<langle>RetVal (Bool False), h\<rangle>"

| RedYield:
  "P,t \<turnstile> \<langle>a\<bullet>yield([]), h\<rangle> -\<lbrace>Yield\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

subsection {* Aggressive formulation for external cals *}

definition red_external_aggr :: 
  "'m prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> 'heap \<Rightarrow> 
  (('addr, 'thread_id, 'heap) external_thread_action \<times> 'addr extCallRet \<times> 'heap) set"
where
  "red_external_aggr P t a M vs h =
   (if M = wait then
      let ad_t = thread_id2addr t
      in {(\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetEXC InterruptedException, h),
          (\<lbrace>Suspend a, Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a\<rbrace>, RetStaySame, h),
          (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, RetEXC IllegalMonitorState, h),
          (\<lbrace>Notified\<rbrace>, RetVal Unit, h),
          (\<lbrace>WokenUp, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetEXC InterruptedException, h)}
    else if M = notify then {(\<lbrace>Notify a, Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>, RetVal Unit, h),
                             (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, RetEXC IllegalMonitorState, h)}
    else if M = notifyAll then {(\<lbrace>NotifyAll a, Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>, RetVal Unit, h),
                                (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, RetEXC IllegalMonitorState, h)}
    else if M = clone then
       {((\<lambda>\<^isup>f [], [], [], [], [], obs), RetVal (Addr a'), h')|obs a' h'. heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>}
       \<union> {(\<lbrace>\<rbrace>, RetEXC OutOfMemory, h')|h'. heap_clone P h a h' None}
    else if M = hashcode then {(\<lbrace>\<rbrace>, RetVal (Intg (word_of_int (hash_addr a))), h)}
    else if M = print then {(\<lbrace>ExternalCall a M vs Unit\<rbrace>, RetVal Unit, h)}
    else if M = currentThread then {(\<lbrace>\<rbrace>, RetVal (Addr (thread_id2addr t)), h)}
    else if M = interrupted then {(\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetVal (Bool True), h),
                                  (\<lbrace>IsInterrupted t False\<rbrace>, RetVal (Bool False), h)}
    else if M = yield then {(\<lbrace>Yield\<rbrace>, RetVal Unit, h)}
    else
      let T = the (typeof_addr h a)
      in if P \<turnstile> T \<le> Class Thread then
        let t_a = addr2thread_id a 
        in if M = start then 
             {(\<lbrace>NewThread t_a (the_Class T, run, a) h, ThreadStart t_a\<rbrace>, RetVal Unit, h), 
              (\<lbrace>ThreadExists t_a True\<rbrace>, RetEXC IllegalThreadState, h)}
           else if M = join then 
             {(\<lbrace>Join t_a, IsInterrupted t False, ThreadJoin t_a\<rbrace>, RetVal Unit, h),
              (\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetEXC InterruptedException, h)}
           else if M = interrupt then 
             {(\<lbrace>ThreadExists t_a True, WakeUp t_a, Interrupt t_a, ObsInterrupt t_a\<rbrace>, RetVal Unit, h), 
              (\<lbrace>ThreadExists t_a False\<rbrace>, RetVal Unit, h)}
           else if M = isInterrupted then
             {(\<lbrace>IsInterrupted t_a False\<rbrace>, RetVal (Bool False), h),
              (\<lbrace>IsInterrupted t_a True, ObsInterrupted t_a\<rbrace>, RetVal (Bool True), h)}
         else undefined
      else undefined)"

lemma red_external_imp_red_external_aggr:
  "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<Longrightarrow> (ta, va, h') \<in> red_external_aggr P t a M vs h"
unfolding red_external_aggr_def
by(auto elim!: red_external.cases split del: split_if simp add: split_beta)

end

context heap begin

lemma hext_heap_copy_loc:
  "heap_copy_loc a a' al h obs h' \<Longrightarrow> h \<unlhd> h'"
by(blast elim: heap_copy_loc.cases dest: hext_heap_ops)

lemma hext_heap_copies:
  assumes "heap_copies a a' als h obs h'"
  shows "h \<unlhd> h'"
using assms by induct(blast intro: hext_heap_copy_loc hext_trans)+

lemma hext_heap_clone:
  assumes "heap_clone P h a h' res"
  shows "h \<unlhd> h'"
using assms by(blast elim: heap_clone.cases dest: hext_heap_ops hext_heap_copies intro: hext_trans)

theorem red_external_hext: 
  assumes "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  shows "hext h h'"
using assms
by(cases)(blast intro: hext_heap_ops hext_heap_clone)+

end

context heap_conf begin

lemma typeof_addr_heap_clone:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "hconf h"
  shows "typeof_addr h' a' = typeof_addr h a"
using assms
by cases (auto dest!: new_obj_SomeD new_arr_SomeD hext_heap_copies dest: typeof_addr_hext_mono typeof_addr_is_type is_type_ArrayD)

end

context heap_base begin 

lemma red_ext_new_thread_heap:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' ex h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = h'"
by(auto elim: red_external.cases simp add: ta_upd_simps)

lemma red_ext_aggr_new_thread_heap:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M; 
    NewThread t' ex h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = h'"
apply(auto simp add: red_external_aggr_def is_native_def2 native_call_def split_beta ta_upd_simps elim!: external_WT_defs.cases)
done

end

context addr_conv begin

lemma red_external_new_thread_exists_thread_object:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' (thread_id2addr t') = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
by(auto elim!: red_external.cases dest!: Array_widen simp add: ta_upd_simps)

lemma red_external_aggr_new_thread_exists_thread_object:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M; typeof_addr h a \<noteq> None;
     NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' (thread_id2addr t') = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(auto simp add: red_external_aggr_def is_native_def2 native_call_def split_beta ta_upd_simps elim!: external_WT_defs_cases split: split_if_asm dest!: Array_widen)
apply(auto elim!: external_WT_defs.cases simp add: widen_Class ta_upd_simps)
done

end

context heap begin

lemma red_external_aggr_hext: 
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; P,h \<turnstile> a\<bullet>M(vs) : U \<rbrakk> \<Longrightarrow> h \<unlhd> h'"
apply(auto simp add: red_external_aggr_def split_beta native_call_def elim!: external_WT'.cases external_WT_defs_cases external_WT.cases split: split_if_asm)
apply(blast intro: hext_heap_ops hext_heap_clone dest: Array_widen elim: external_WT_defs.cases)+
done

lemma red_external_aggr_preserves_tconf:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M;
     P,h \<turnstile> t' \<surd>t \<rbrakk>
  \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
apply(auto simp add: red_external_aggr_def split_beta tconf_def split: split_if_asm)
apply(blast dest: hext_heap_ops hext_heap_clone typeof_addr_hext_mono)+
apply(auto simp add: is_native_def2 native_call_def elim!: external_WT_defs.cases)
done

end

context heap_base begin

lemma red_external_Wakeup_no_Join_no_Lock_no_Interrupt:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow>
  collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = {} \<and> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = {}"
by(auto elim!: red_external.cases simp add: ta_upd_simps collect_locks_def collect_interrupts_def)

lemma red_external_aggr_Wakeup_no_Join:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M; 
     Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = {} \<and> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = {}"
apply(auto simp add: red_external_aggr_def is_native_def2 native_call_def split_beta ta_upd_simps split: split_if_asm)
apply(auto elim!: external_WT_defs.cases simp add: ta_upd_simps collect_locks_def collect_interrupts_def)
done

lemma red_external_Suspend_StaySame:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> va = RetStaySame"
by(auto elim!: red_external.cases simp add: ta_upd_simps)

lemma red_external_aggr_Suspend_StaySame:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M;
     Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> va = RetStaySame" 
apply(auto simp add: red_external_aggr_def is_native_def2 native_call_def split_beta ta_upd_simps split: split_if_asm)
apply(auto elim!: external_WT_defs.cases simp add: ta_upd_simps)
done

lemma red_external_Suspend_waitD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> M = wait"
by(auto elim!: red_external.cases simp add: ta_upd_simps)

lemma red_external_aggr_Suspend_waitD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M;
     Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> M = wait"
apply(auto simp add: red_external_aggr_def is_native_def2 native_call_def split_beta ta_upd_simps split: split_if_asm)
apply(auto elim!: external_WT_defs.cases simp add: ta_upd_simps)
done

lemma red_external_new_thread_sub_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M' = run"
by(auto elim!: red_external.cases simp add: widen_Class ta_upd_simps)

lemma red_external_aggr_new_thread_sub_thread:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M; typeof_addr h a \<noteq> None;
     NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M' = run"
apply(auto simp add: red_external_aggr_def is_native_def2 native_call_def split_beta ta_upd_simps elim!: external_WT_defs_cases split: split_if_asm dest!: Array_widen)
apply(auto elim!: external_WT_defs.cases simp add: widen_Class ta_upd_simps)
done

end

context heap begin

lemma red_external_preserves_tconf:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; P,h \<turnstile> t' \<surd>t \<rbrakk> \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
by(drule red_external_hext)(rule tconf_hext_mono)

end

subsection {* @{text "\<tau>"}-moves *}

inductive \<tau>external_defs :: "ty \<Rightarrow> mname \<Rightarrow> bool"
where
  "\<tau>external_defs (Class Object) hashcode"
| "\<tau>external_defs (Class Object) currentThread"

definition \<tau>external :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> bool"
where "\<tau>external P T M \<longleftrightarrow> (\<exists>Ts Tr T'. P \<turnstile> T native M:Ts\<rightarrow>Tr in T' \<and> \<tau>external_defs T' M)"

context heap_base begin

definition \<tau>external' :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> bool"
where "\<tau>external' P h a M \<longleftrightarrow> (\<exists>T. typeof_addr h a = Some T \<and> \<tau>external P T M)"

lemma \<tau>external'_red_external_heap_unchanged:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; \<tau>external' P h a M \<rbrakk> \<Longrightarrow> h' = h"
by(auto elim!: red_external.cases \<tau>external_defs.cases simp add: \<tau>external_def \<tau>external'_def)

lemma \<tau>external'_red_external_aggr_heap_unchanged:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; \<tau>external' P h a M \<rbrakk> \<Longrightarrow> h' = h"
by(auto elim!: \<tau>external_defs.cases simp add: \<tau>external_def \<tau>external'_def red_external_aggr_def)

lemma \<tau>external'_red_external_TA_empty:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; \<tau>external' P h a M \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
by(auto elim!: red_external.cases \<tau>external_defs.cases simp add: \<tau>external_def \<tau>external'_def)

lemma \<tau>external'_red_external_aggr_TA_empty:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; \<tau>external' P h a M \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
by(auto elim!: \<tau>external_defs.cases simp add: \<tau>external_def \<tau>external'_def red_external_aggr_def)

lemma red_external_new_thread_addr_conf:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; NewThread t (C, M, a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> P,h' \<turnstile> Addr a :\<le> Class Thread"
by(auto elim!: red_external.cases simp add: conf_def ta_upd_simps)

lemma \<tau>external_red_external_aggr_heap_unchanged:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; \<tau>external P (the (typeof_addr h a)) M \<rbrakk> \<Longrightarrow> h' = h"
by(auto elim!: \<tau>external_defs.cases simp add: \<tau>external_def red_external_aggr_def)

lemma \<tau>external_red_external_aggr_TA_empty:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; \<tau>external P (the (typeof_addr h a)) M \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
by(auto elim!: \<tau>external_defs.cases simp add: \<tau>external_def red_external_aggr_def)

end

definition native_method :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> ty \<times> ty list \<times> ty"
where "native_method P T M = (THE(T', Ts, Tr). P \<turnstile> T native M:Ts \<rightarrow> Tr in T')"

lemma native_method_def2 [simp]: 
  "P \<turnstile> T native M:Ts \<rightarrow> Tr in T' \<Longrightarrow> native_method P T M = (T', Ts, Tr)"
by(auto simp add: native_method_def dest: native_call_fun)

subsection {* Code generation *}

code_pred 
  (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  external_WT_defs 
.

code_pred
  (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  native_call
.

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  is_native
.

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  external_WT 
.

lemma eval_external_WT_i_i_i_o_o_conv:
  "Predicate.eval (external_WT_i_i_i_o_o P T M) (Ts, U) \<longleftrightarrow> P \<turnstile> T\<bullet>M(Ts) :: U"
by(auto elim: external_WT_i_i_i_o_oE intro: external_WT_i_i_i_o_oI)

declare heap_base.heap_copy_loc.intros[code_pred_intro]

code_pred
  (modes: (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) 
  heap_base.heap_copy_loc
proof -
  case heap_copy_loc
  from heap_copy_loc.prems show thesis
    by(rule heap_base.heap_copy_loc.cases)(rule that[OF refl refl refl refl refl refl])
qed

declare heap_base.heap_copies.intros [code_pred_intro]

code_pred
  (modes: (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) => (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  heap_base.heap_copies
proof -
  case heap_copies
  from heap_copies.prems show thesis
    by(rule heap_base.heap_copies.cases)(erule (3) that[OF refl refl refl refl]|assumption)+
qed

declare heap_base.heap_clone.intros [code_pred_intro]

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  heap_base.heap_clone
proof -
  case heap_clone
  from heap_clone.prems show thesis
    by(rule heap_base.heap_clone.cases)(erule (3) that[OF refl refl refl refl refl refl refl refl refl]|assumption)+
qed

declare heap_base.red_external.intros[code_pred_intro]

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  heap_base.red_external
proof -
  case red_external
  from red_external.prems show ?thesis
    apply(rule heap_base.red_external.cases)
    apply(erule (4) that[OF refl refl refl refl refl refl refl refl refl refl refl refl refl]|assumption)+
    done
qed

lemma eval_native_call_i_i_i_o_o_o_conv:
  "Predicate.eval (native_call_i_i_i_o_o_o P T M) = (\<lambda>(Ts, Tr, T'). P \<turnstile> T native M:Ts\<rightarrow>Tr in T')"
by(auto intro: native_call_i_i_i_o_o_oI elim: native_call_i_i_i_o_o_oE intro!: ext)

lemma native_method_code [code]:
  "native_method P T M = Predicate.the (native_call_i_i_i_o_o_o P T M \<guillemotright>= (\<lambda>(Ts, Tr, T'). Predicate.single (T', Ts, Tr)))"
apply(rule sym, rule the_eqI)
apply (simp add: native_method_def eval_native_call_i_i_i_o_o_o_conv)
apply (rule arg_cong [where f=The])
apply (auto simp add: SUPR_def Sup_fun_def Sup_bool_def fun_eq_iff)
done

end