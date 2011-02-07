(*  Title:      JinjaThreads/Common/ExternalCall.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of method calls that cannot be defined inside JinjaThreads} *}

theory ExternalCall imports
  "../Framework/FWLocking"
  Conform
begin

types
  'heap external_thread_action = "(cname \<times> mname \<times> addr,'heap) Jinja_thread_action"

translations
  (type) "'heap external_thread_action" <= (type) "(String.literal \<times> String.literal \<times> nat,'heap) Jinja_thread_action"

subsection {* Typing of external calls *}

inductive external_WT_defs :: "ty \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> bool" ("(_\<bullet>_'(_')) :: _" [50, 0, 0, 50] 60)
where
  "Class Thread\<bullet>start([]) :: Void"
| "Class Thread\<bullet>join([]) :: Void"
| "Class Thread\<bullet>interrupt([]) :: Void"
| "Class Object\<bullet>wait([]) :: Void"
| "Class Object\<bullet>notify([]) :: Void"
| "Class Object\<bullet>notifyAll([]) :: Void"
| "Class Object\<bullet>clone([]) :: Class Object"
| "Class Object\<bullet>equals([Class Object]) :: Boolean"
| "Class Object\<bullet>hashcode([]) :: Integer"
| "Class Object\<bullet>toString([]) :: Class String"

definition is_external_call :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> bool"
where 
  "is_external_call P T M \<longleftrightarrow>
   (\<exists>T'. P \<turnstile> T \<le> T' \<and> (\<exists>Ts U. T'\<bullet>M(Ts) :: U) \<and> T \<noteq> NT \<and>
         (case T of Class C \<Rightarrow> \<not> P \<turnstile> C has M | _ \<Rightarrow> True))"

inductive external_WT :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> (_\<bullet>_'(_')) :: _" [50, 0, 0, 50] 60)
where "\<lbrakk> T'\<bullet>M(Ts) :: U; P \<turnstile> T \<le> T'; is_external_call P T M \<rbrakk> \<Longrightarrow> P \<turnstile> T\<bullet>M(Ts) :: U"

inductive (in heap_base) external_WT' :: "'m prog \<Rightarrow> 'heap \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> ty \<Rightarrow> bool"
  ("_,_ \<turnstile> (_\<bullet>_'(_')) : _" [50,0,0,0,50] 60)
for P :: "'m prog" and h :: 'heap and a :: addr and M :: mname and vs :: "val list" and U :: ty
where "\<lbrakk> typeof_addr h a = \<lfloor>T\<rfloor>; map typeof\<^bsub>h\<^esub> vs = map Some Ts; P \<turnstile> T\<bullet>M(Ts') :: U; P \<turnstile> Ts [\<le>] Ts' \<rbrakk> \<Longrightarrow> P,h \<turnstile> a\<bullet>M(vs) : U"

inductive_cases external_WT_defs_cases:
  "a\<bullet>start(vs) :: T"
  "a\<bullet>join(vs) :: T"
  "a\<bullet>interrupt(vs) :: T"
  "a\<bullet>wait(vs) :: T"
  "a\<bullet>notify(vs) :: T"
  "a\<bullet>notifyAll(vs) :: T"
  "a\<bullet>clone(vs) :: T"
  "a\<bullet>equals(vs) :: T"
  "a\<bullet>hashcode(vs) :: T"
  "a\<bullet>toString(vs) :: T"

lemma is_external_callI:
  "\<lbrakk> P \<turnstile> T \<le> T'; T'\<bullet>M(Ts) :: U; T \<noteq> NT;
    \<And>C. \<lbrakk> T = Class C; P \<turnstile> C has M \<rbrakk> \<Longrightarrow> False \<rbrakk>
  \<Longrightarrow> is_external_call P T M"
by(auto simp add: is_external_call_def split: ty.split)

lemma external_call_not_sees_method:
  "\<lbrakk> P \<turnstile> C sees M: Ts \<rightarrow> T = mthd in D; is_external_call P (Class C) M \<rbrakk>
  \<Longrightarrow> False"
by(auto simp add: is_external_call_def has_method_def)

lemma external_WT_determ:
  "\<lbrakk> P \<turnstile> T\<bullet>M(Ts) :: U; P \<turnstile> T\<bullet>M(Ts') :: U' \<rbrakk> \<Longrightarrow> Ts = Ts' \<and> U = U'"
by(auto elim!: external_WT_defs.cases external_WT.cases)

lemma external_WT_The_conv:
  "P \<turnstile> T\<bullet>M(TS) :: U \<Longrightarrow> (THE U. P \<turnstile> T\<bullet>M(TS) :: U) = U"
by(auto dest: external_WT_determ)

lemma external_WT_The_Ex_conv:
  "P \<turnstile> T\<bullet>M(TS) :: U \<Longrightarrow> (THE U. \<exists>TS. P \<turnstile> T\<bullet>M(TS) :: U) = U"
by(auto dest: external_WT_determ)

lemma external_WT_The_Ex_conv2:
  "\<lbrakk> P \<turnstile> T\<bullet>M(Ts') :: U; P \<turnstile> Ts [\<le>] Ts' \<rbrakk> \<Longrightarrow> (THE U. \<exists>Ts'. P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T\<bullet>M(Ts') :: U) = U"
by(auto dest: external_WT_determ)

lemma is_external_call_widen_mono:
  "\<lbrakk> is_external_call P T M; P \<turnstile> T' \<le> T; case T' of Class C \<Rightarrow> \<not> P \<turnstile> C has M | NT \<Rightarrow> False | _ \<Rightarrow> True \<rbrakk>
  \<Longrightarrow> is_external_call P T' M"
apply(auto simp add: is_external_call_def split: ty.split intro: widen_trans)
apply(auto intro: widen_trans)
done

lemma external_WT_widen_mono:
  "\<lbrakk> P \<turnstile> T\<bullet>M(Ts) :: U; P \<turnstile> T' \<le> T; case T' of Class C \<Rightarrow> \<not> P \<turnstile> C has M | NT \<Rightarrow> False | _ \<Rightarrow> True \<rbrakk> 
  \<Longrightarrow> \<exists>U'. P \<turnstile> T'\<bullet>M(Ts) :: U' \<and> P \<turnstile> U' \<le> U"
by(auto split: ty.split_asm elim!: external_WT.cases is_external_call_widen_mono intro!: external_WT.intros intro: widens_trans widen_trans)

lemma external_WT_is_external_call:
  "P \<turnstile> T\<bullet>M(Ts) :: U \<Longrightarrow> is_external_call P T M"
by(auto elim: external_WT.cases)

lemma external_WT_not_NT:
  "P \<turnstile> T\<bullet>M(Ts) :: U \<Longrightarrow> T \<noteq> NT"
by(auto elim!: external_WT.cases simp add: is_external_call_def)

lemma is_external_call_is_refT: "is_external_call P T M \<Longrightarrow> is_refT T"
by(auto simp add: is_external_call_def elim!: external_WT_defs.cases intro: widen_refT)

lemma not_is_external_call_NT [simp]: "\<not> is_external_call P NT M"
by(simp add: is_external_call_def)

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

datatype extCallRet = 
    RetVal val
  | RetExc addr
  | RetStaySame

lemma extCallRet_rec [simp]: "extCallRet_rec = extCallRet_case"
by(auto simp add: fun_eq_iff split: extCallRet.split)

abbreviation interrupted_flag_loc 
where "interrupted_flag_loc \<equiv> CField Thread interrupted_flag"

context heap_base begin

abbreviation RetEXC :: "cname \<Rightarrow> extCallRet"
where "RetEXC C \<equiv> RetExc (addr_of_sys_xcpt C)"

inductive heap_copy_loc :: "addr \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> 'heap \<Rightarrow> obs_event list \<Rightarrow> 'heap \<Rightarrow> bool"
for a :: addr and a' :: addr and al :: addr_loc and h :: 'heap
where
  "\<lbrakk> heap_read h a al v; heap_write h a' al v h' \<rbrakk>
  \<Longrightarrow> heap_copy_loc a a' al h ([ReadMem a al v, WriteMem a' al v]) h'"

inductive heap_copies :: "addr \<Rightarrow> addr \<Rightarrow> addr_loc list \<Rightarrow> 'heap \<Rightarrow> obs_event list \<Rightarrow> 'heap \<Rightarrow> bool"
for a :: addr and a' :: addr
where
  Nil: "heap_copies a a' [] h [] h"
| Cons:
  "\<lbrakk> heap_copy_loc a a' al h ob h'; heap_copies a a' als h' obs h'' \<rbrakk>
  \<Longrightarrow> heap_copies a a' (al # als) h (ob @ obs) h''"

inductive_cases heap_copies_cases:
  "heap_copies a a' [] h ops h'"
  "heap_copies a a' (al#als) h ops h'"

-- {*
  Cloning an interrupted thread yields an interrupted thread (cf. Sun JVM 1.6.0\_07).
  Since the interrupt flag is stored inside the thread object, heap\_clone correctly copies the interrupt status.
  However, we do not use fields for thread id or whether it has been started yet. 
  Starting a clone of a started thread with Sun JVM 1.6.0\_07 raises an illegal thread state exception,
  we just start another thread.
  The thread at \texttt{http://mail.openjdk.java.net/pipermail/core-libs-dev/2010-August/004715.html} discusses 
  the general problem of thread cloning and argues against that.
  The bug report \texttt{http://bugs.sun.com/bugdatabase/view\_bug.do?bug\_id=6968584} 
  changes the Thread class implementation
  such that \texttt{Object.clone()} can no longer be accessed for Thread and subclasses.

  Array cells are never volatile themselves.
  *}

inductive heap_clone :: "'m prog \<Rightarrow> 'heap \<Rightarrow> addr \<Rightarrow> 'heap \<Rightarrow> (obs_event list \<times> addr) option \<Rightarrow> bool"
for P :: "'m prog" and h :: 'heap and a :: addr 
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
  "\<lbrakk> typeof_addr h a = \<lfloor>Array T\<rfloor>; n = array_length h a; new_arr h T n = (h', \<lfloor>a'\<rfloor>);
     heap_copies a a' (map ACell [0..<n]) h' obs  h'' \<rbrakk>
  \<Longrightarrow> heap_clone P h a h'' \<lfloor>(NewArr a' T n # obs, a')\<rfloor>"


inductive red_external :: "'m prog \<Rightarrow> thread_id \<Rightarrow> 'heap \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> 'heap external_thread_action \<Rightarrow> extCallRet \<Rightarrow> 'heap \<Rightarrow> bool"
  and red_external_syntax :: "'m prog \<Rightarrow> thread_id \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> 'heap \<Rightarrow> 'heap external_thread_action \<Rightarrow> extCallRet \<Rightarrow> 'heap \<Rightarrow> bool"
  ("_,_ \<turnstile> (\<langle>(_\<bullet>_'(_')),/_\<rangle>) -_\<rightarrow>ext (\<langle>(_),/(_)\<rangle>)" [50, 0, 0, 0, 0, 0, 0, 0, 0] 51)
for P :: "'m prog" and t :: thread_id and h :: 'heap and a :: addr
where
  "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<equiv> red_external P t h a M vs ta va h'"

| RedNewThread:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>start([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread a (C, run, a) h\<rbrace>\<lbrace>\<^bsub>o\<^esub> ThreadStart a \<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNewThreadFail:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>start([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists a\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalThreadState, h\<rangle>"

| RedJoin:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>join([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Join a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ThreadJoin a\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

    -- {* 
    Interruption should produce inter-thread actions (JLS 17.4.4) for the synchronizes-with order.
    They should synchronize with the inter-thread actions that determine whether a thread has been interrupted.
    Hence, interruption generates volatile heap write actions, which synchronize with all (volatile) read
    actions on the interrupt flag.
    *}
  
| RedInterrupt:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread;
     heap_write h a interrupted_flag_loc (Bool True) h' \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>interrupt([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Interrupt a\<rbrace>\<lbrace>\<^bsub>o\<^esub> WriteMem a interrupted_flag_loc (Bool True)\<rbrace>\<rightarrow>ext
            \<langle>RetVal Unit, h'\<rangle>"

    -- {*
    The JLS leaves unspecified whether wait first checks for the monitor state
    (whether the thread holds a lock on the monitor) or for the interrupt flag of the current thread.
    Sun's JVM 1.6.0\_07 seems to first check for the monitor state, so we do it here, too.
    *}
| RedWaitInterrupt:
  "\<lbrakk> typeof_addr h t = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread;
     heap_read h t interrupted_flag_loc (Bool True);
     heap_write h t interrupted_flag_loc (Bool False) h' \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>
                             \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True),
                                WriteMem t interrupted_flag_loc (Bool False)\<rbrace> \<rightarrow>ext 
            \<langle>RetEXC InterruptedException, h'\<rangle>"

| RedWait:
  "\<lbrakk> typeof_addr h t = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread;
     heap_read h t interrupted_flag_loc (Bool False) \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Suspend a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a \<rbrace>
                             \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool False), SyncUnlock a \<rbrace>\<rightarrow>ext 
            \<langle>RetStaySame, h\<rangle>"

| RedWaitFail:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedWaitNotified:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notified \<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

    -- {*
    This rule does NOT check that the interrupted flag is set. Still, it reads from the interrupted flag
    to induce a synchronizes-with edge from
    the last write to the interrupted flag.
    Under the assumption that only a thread itself is able to clear its interrupted flag, we know that
    the flag must always be set when this rule can be chosen by the multithreaded semantics.
    The class Thread in Java is implemented such that this assumption is satsified, which we do not model explicitly.
    *}
| RedWaitInterrupted:
  "\<lbrakk> typeof_addr h t = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread;
     heap_read h t interrupted_flag_loc (Bool b);
     heap_write h t interrupted_flag_loc (Bool False) h' \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Interrupted \<rbrace>
                            \<lbrace>\<^bsub>o\<^esub>  ReadMem t interrupted_flag_loc (Bool b),
                                WriteMem t interrupted_flag_loc (Bool False)\<rbrace>\<rightarrow>ext
           \<langle>RetEXC InterruptedException, h'\<rangle>"

    -- {*
    notify and notifyAll do not perform synchronization inter-thread actions
    because they only tests whether the thread holds a lock, but does not change the lock state.
    *}

| RedNotify:
  "P,t \<turnstile> \<langle>a\<bullet>notify([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notify a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNotifyFail:
  "P,t \<turnstile> \<langle>a\<bullet>notify([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedNotifyAll:
  "P,t \<turnstile> \<langle>a\<bullet>notifyAll([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> NotifyAll a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNotifyAllFail:
  "P,t \<turnstile> \<langle>a\<bullet>notifyAll([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedClone:
  "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor> \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>clone([]), h\<rangle> -(\<lambda>\<^isup>f [], [], [], [], obs)\<rightarrow>ext \<langle>RetVal (Addr a'), h'\<rangle>"

| RedCloneFail:
  "heap_clone P h a h' None \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>clone([]), h\<rangle> -\<epsilon>\<rightarrow>ext \<langle>RetEXC OutOfMemory, h'\<rangle>"

| RedEquals:
  "P,t \<turnstile> \<langle>a\<bullet>equals([v]), h\<rangle> -\<epsilon>\<rightarrow>ext \<langle>RetVal (Bool (Addr a = v)), h\<rangle>"

| RedHashcode:
  "P,t \<turnstile> \<langle>a\<bullet>hashcode([]), h\<rangle> -\<epsilon>\<rightarrow>ext \<langle>RetVal (Intg (word_of_int (int a))), h\<rangle>"

| RedToString:
  "P,t \<turnstile> \<langle>a\<bullet>toString([]), h\<rangle> -\<epsilon>\<rightarrow>ext \<langle>RetVal Null, h\<rangle>"

subsection {* Aggressive formulation for external cals *}

definition red_external_aggr :: "'m prog \<Rightarrow> thread_id \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> 'heap \<Rightarrow> ('heap external_thread_action \<times> extCallRet \<times> 'heap) set"
where
  "red_external_aggr P t a M vs h =
   (if M = wait then
       (if heap_read h t interrupted_flag_loc (Bool True) 
        then {(\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), 
                                      WriteMem t interrupted_flag_loc (Bool False) \<rbrace>,
               RetEXC InterruptedException, h')|h'. heap_write h t interrupted_flag_loc (Bool False) h'}
        else {})
       \<union>
       (if heap_read h t interrupted_flag_loc (Bool False)
        then {(\<epsilon>\<lbrace>\<^bsub>w\<^esub> Suspend a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a \<rbrace>
                \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool False), SyncUnlock a \<rbrace>, RetStaySame, h)}
        else {})
       \<union>
       {(\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, RetEXC IllegalMonitorState, h),
        (\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notified \<rbrace>, RetVal Unit, h)}
       \<union>
       {(\<epsilon>\<lbrace>\<^bsub>w\<^esub> Interrupted \<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool b), 
                            WriteMem t interrupted_flag_loc (Bool False)\<rbrace>,
         RetEXC InterruptedException, h')
        |b h'. heap_read h t interrupted_flag_loc (Bool b) \<and> heap_write h t (CField Thread interrupted_flag) (Bool False) h'}
    else if M = notify then {(\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notify a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>, RetVal Unit, h),
                             (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, RetEXC IllegalMonitorState, h)}
    else if M = notifyAll then {(\<epsilon>\<lbrace>\<^bsub>w\<^esub> NotifyAll a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>, RetVal Unit, h),
                                 (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, RetEXC IllegalMonitorState, h)}
    else if M = clone then
       {((\<lambda>\<^isup>f [], [], [], [], obs), RetVal (Addr a'), h')|obs a' h'. heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>}
       \<union> {(\<epsilon>, RetEXC OutOfMemory, h')|h'. heap_clone P h a h' None}
    else if M = equals then {(\<epsilon>, RetVal (Bool (Addr a = hd vs)), h)}
    else if M = hashcode then {(\<epsilon>, RetVal (Intg (word_of_int (int a))), h)}
    else if M = toString then {(\<epsilon>, RetVal Null, h)}
    else if P \<turnstile> the (typeof_addr h a) \<le> Class Thread then
         if M = start then {(\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread a (the_Class (the (typeof_addr h a)), run, a) h\<rbrace>\<lbrace>\<^bsub>o\<^esub> ThreadStart a\<rbrace>, RetVal Unit, h), 
                            (\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists a\<rbrace>, RetEXC IllegalThreadState, h)}
         else if M = join then {(\<epsilon>\<lbrace>\<^bsub>c\<^esub> Join a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ThreadJoin a\<rbrace>, RetVal Unit, h)}
         else if M = interrupt then
              {(\<epsilon>\<lbrace>\<^bsub>w\<^esub> Interrupt a\<rbrace>\<lbrace>\<^bsub>o\<^esub> WriteMem a interrupted_flag_loc (Bool True)\<rbrace>, RetVal Unit, h')
               |h'. heap_write h a interrupted_flag_loc (Bool True) h'}
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

lemma typeof_addr_heap_clone:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  shows "typeof_addr h' a' = typeof_addr h a"
using assms
by cases (auto dest!: new_obj_SomeD new_arr_SomeD hext_heap_copies dest: typeof_addr_hext_mono)

end

context heap_base begin 

lemma red_ext_new_thread_heap:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' ex h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = h'"
by(auto elim: red_external.cases simp add: ta_upd_simps)

lemma red_ext_aggr_new_thread_heap:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_external_call P (the (typeof_addr h a)) M; 
    NewThread t' ex h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = h'"
apply(auto simp add: red_external_aggr_def is_external_call_def split_beta ta_upd_simps elim!: external_WT_defs.cases)
apply(auto split: split_if_asm simp add: ta_upd_simps)
done

lemma red_external_new_thread_exists_thread_object:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' t' = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
by(auto elim!: red_external.cases dest!: Array_widen simp add: ta_upd_simps)

lemma red_external_aggr_new_thread_exists_thread_object:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_external_call P (the (typeof_addr h a)) M; typeof_addr h a \<noteq> None;
     NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' t' = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(auto simp add: red_external_aggr_def is_external_call_def split_beta ta_upd_simps elim!: external_WT_defs_cases split: split_if_asm dest!: Array_widen)
apply(auto elim!: external_WT_defs.cases simp add: widen_Class ta_upd_simps)
done

end

context heap begin

lemma red_external_aggr_hext: 
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; P,h \<turnstile> a\<bullet>M(vs) : U \<rbrakk> \<Longrightarrow> h \<unlhd> h'"
apply(auto simp add: red_external_aggr_def split_beta elim!: external_WT'.cases external_WT_defs_cases external_WT.cases split: split_if_asm)
apply(blast intro: hext_heap_ops hext_heap_clone dest: Array_widen elim: external_WT_defs.cases)+
done

lemma red_external_aggr_preserves_tconf:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_external_call P (the (typeof_addr h a)) M;
     P,h \<turnstile> t' \<surd>t \<rbrakk>
  \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
apply(auto simp add: red_external_aggr_def split_beta tconf_def split: split_if_asm)
apply(blast dest: hext_heap_ops hext_heap_clone typeof_addr_hext_mono)+
apply(auto simp add: is_external_call_def elim!: external_WT_defs.cases)
done

end

context heap_base begin

lemma red_external_Wakeup_no_Join_no_Lock:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> Interrupted \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow>
  \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = [] \<and> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {}"
by(auto elim!: red_external.cases simp add: ta_upd_simps collect_locks_def)

lemma red_external_aggr_Wakeup_no_Join:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_external_call P (the (typeof_addr h a)) M; 
     Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> Interrupted \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = [] \<and> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {}"
apply(auto simp add: red_external_aggr_def is_external_call_def split_beta ta_upd_simps split: split_if_asm)
apply(auto elim!: external_WT_defs.cases simp add: ta_upd_simps collect_locks_def)
done

lemma red_external_Suspend_StaySame:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> va = RetStaySame"
by(auto elim!: red_external.cases simp add: ta_upd_simps)

lemma red_external_aggr_Suspend_StaySame:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_external_call P (the (typeof_addr h a)) M;
     Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> va = RetStaySame" 
apply(auto simp add: red_external_aggr_def is_external_call_def split_beta ta_upd_simps split: split_if_asm)
apply(auto elim!: external_WT_defs.cases simp add: ta_upd_simps)
done

lemma red_external_Suspend_waitD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> M = wait"
by(auto elim!: red_external.cases simp add: ta_upd_simps)

lemma red_external_aggr_Suspend_waitD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_external_call P (the (typeof_addr h a)) M;
     Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> M = wait"
apply(auto simp add: red_external_aggr_def is_external_call_def split_beta ta_upd_simps split: split_if_asm)
apply(auto elim!: external_WT_defs.cases simp add: ta_upd_simps)
done

lemma red_external_new_thread_sub_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M' = run"
by(auto elim!: red_external.cases simp add: widen_Class ta_upd_simps)

end


context heap begin

lemma red_external_preserves_tconf:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; P,h \<turnstile> t' \<surd>t \<rbrakk> \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
by(drule red_external_hext)(rule tconf_hext_mono)

end

subsection {* @{text "\<tau>"}-moves *}

inductive \<tau>external_defs :: "ty \<Rightarrow> mname \<Rightarrow> bool"
where
  "\<tau>external_defs (Class Object) equals"
| "\<tau>external_defs (Class Object) hashcode"

definition \<tau>external :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> bool"
where "\<tau>external P T M \<longleftrightarrow> (\<exists>T'. P \<turnstile> T' \<le> T \<and> \<tau>external_defs T M) \<and> is_external_call P T M"

context heap_base begin

definition \<tau>external' :: "'m prog \<Rightarrow> 'heap \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> bool"
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

subsection {* Code generation *}

code_pred external_WT_defs .

lemma is_external_call_code [code]:
  "is_external_call P T M =
   Predicate.holds (Predicate.bind (external_WT_defs_o_i_o_o M) 
                                   (\<lambda>(T', Ts, U). if T \<noteq> NT \<and> P \<turnstile> T \<le> T' \<and> (case T of Class C \<Rightarrow> \<not> P \<turnstile> C has M | _ \<Rightarrow> True)
                                         then Predicate.single ()
                                         else bot))"
unfolding is_external_call_def
apply(rule iffI)
 apply clarify
 apply(unfold holds_eq)
 apply(rule bindI)
  apply(erule external_WT_defs_o_i_o_oI)
 apply(simp add: singleI)
apply(erule bindE)
apply(clarsimp split: split_if_asm)
apply(auto elim: botE external_WT_defs_o_i_o_oE)
done

code_pred external_WT . 

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
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  heap_base.red_external
proof -
  case red_external
  from red_external.prems show ?thesis
    apply(rule heap_base.red_external.cases)
    apply(erule (4) that[OF refl refl refl refl refl refl refl refl refl refl refl]|assumption)+
    done
qed

end