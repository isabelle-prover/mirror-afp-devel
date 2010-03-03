(*  Title:      JinjaThreads/Common/ExternalCall.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of method calls that cannot be defined inside JinjaThreads} *}


theory ExternalCall imports
  Exceptions
  "../Framework/FWState"
  Observable_Events
begin

types
  external_thread_action = "(addr,thread_id,cname \<times> mname \<times> addr,heap,addr, obs_event option) thread_action"

translations
  (type) "external_thread_action" <= (type) "(nat,nat,char list \<times> char list \<times> nat,heap,nat, obs_event option) thread_action"

inductive is_external_call :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> bool"
for P :: "'m prog"
where
  ecThreadStart: "P \<turnstile> C \<preceq>\<^sup>* Thread \<Longrightarrow> is_external_call P (Class C) start"
| ecThreadJoin: "P \<turnstile> C \<preceq>\<^sup>* Thread \<Longrightarrow> is_external_call P (Class C) join"
| ecObjectWait: "is_refT T \<Longrightarrow> is_external_call P T wait"
| ecObjectNotify: "is_refT T \<Longrightarrow> is_external_call P T notify"
| ecObjectNotifyAll: "is_refT T \<Longrightarrow> is_external_call P T notifyAll"

lemma is_external_call_is_refT: "is_external_call P T M \<Longrightarrow> is_refT T"
by(auto elim: is_external_call.cases)

lemma is_external_call_widen_mono:
  "\<lbrakk> is_external_call P T M; P \<turnstile> T' \<le> T; T' \<noteq> NT \<rbrakk> \<Longrightarrow> is_external_call P T' M"
by(fastsimp elim!: is_external_call.cases intro: is_external_call.intros rtranclp_trans widen_refT simp add: widen_Class)


subsection {* Semantics of external calls *}

inductive red_external :: "'m prog \<Rightarrow> heap \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> external_thread_action \<Rightarrow> (val + addr) \<Rightarrow> heap \<Rightarrow> bool"
  and red_external_syntax :: "'m prog \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> heap \<Rightarrow> external_thread_action \<Rightarrow> (val + addr) \<Rightarrow> heap \<Rightarrow> bool"
  ("_ \<turnstile> (\<langle>(_\<bullet>_'(_')),/_\<rangle>) -_\<rightarrow>ext (\<langle>(_),/(_)\<rangle>)" [50, 0, 0, 0, 0, 0, 0, 0] 51)
for P :: "'m prog" and h :: heap and a :: addr
where
  "P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<equiv> red_external P h a M vs ta va h'"

| RedNewThread:
  "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>start([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread a (C, run, a) h\<rbrace>\<lbrace>\<^bsub>o\<^esub> ThreadStart a \<rbrace>\<rightarrow>ext \<langle>Inl Unit, h\<rangle>"

| RedNewThreadFail:
  "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>start([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists a\<rbrace>\<rightarrow>ext \<langle>Inr (addr_of_sys_xcpt IllegalThreadState), h\<rangle>"

| RedJoin:
  "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>join([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Join a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ThreadJoin a\<rbrace>\<rightarrow>ext \<langle>Inl Unit, h\<rangle>"

| RedWait:
  "P \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Suspend a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow>ext \<langle>Inl Unit, h\<rangle>"

| RedWaitFail:
  "P \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow>ext \<langle>Inr (addr_of_sys_xcpt IllegalMonitorState), h\<rangle>"

| RedNotify:
  "P \<turnstile> \<langle>a\<bullet>notify([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notify a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow>ext \<langle>Inl Unit, h\<rangle>"

| RedNotifyFail:
  "P \<turnstile> \<langle>a\<bullet>notify([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow>ext \<langle>Inr (addr_of_sys_xcpt IllegalMonitorState), h\<rangle>"

| RedNotifyAll:
  "P \<turnstile> \<langle>a\<bullet>notifyAll([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> NotifyAll a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>\<rightarrow>ext \<langle>Inl Unit, h\<rangle>"

| RedNotifyAllFail:
  "P \<turnstile> \<langle>a\<bullet>notifyAll([]), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>\<rightarrow>ext \<langle>Inr (addr_of_sys_xcpt IllegalMonitorState), h\<rangle>"

subsection {* Aggressive formulation for external calls *}

definition red_external_list :: "'m prog \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> heap \<Rightarrow> (external_thread_action \<times> (val + addr) \<times> heap) list"
where
  "red_external_list P a M vs h =
     (if M = wait then [(\<epsilon>\<lbrace>\<^bsub>w\<^esub> Suspend a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>, Inl Unit, h),
                        (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, Inr (addr_of_sys_xcpt IllegalMonitorState), h)]
      else if M = notify then [(\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notify a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>, Inl Unit, h),
                               (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, Inr (addr_of_sys_xcpt IllegalMonitorState), h)]
      else if M = notifyAll then [(\<epsilon>\<lbrace>\<^bsub>w\<^esub> NotifyAll a \<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a\<rbrace>, Inl Unit, h),
                                  (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, Inr (addr_of_sys_xcpt IllegalMonitorState), h)]
      else if P \<turnstile> the (typeof\<^bsub>h\<^esub> (Addr a)) \<le> Class Thread then
           if M = start then [(\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread a (fst (the_obj (the (h a))), run, a) h\<rbrace>\<lbrace>\<^bsub>o\<^esub> ThreadStart a\<rbrace>, Inl Unit, h), 
                              (\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists a\<rbrace>, Inr (addr_of_sys_xcpt IllegalThreadState), h)]
           else if M = join then [(\<epsilon>\<lbrace>\<^bsub>c\<^esub> Join a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ThreadJoin a\<rbrace>, Inl Unit, h)] else []
      else undefined)"

lemma red_external_imp_red_external_list:
  "P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<Longrightarrow> (ta, va, h') \<in> set (red_external_list P a M vs h)"
unfolding red_external_list_def by(auto elim!: red_external.cases split: heapobj.splits)

lemma red_external_list_not_Nil:
  "is_external_call P (the (typeof\<^bsub>h\<^esub> (Addr a))) M \<Longrightarrow> red_external_list P a M vs h \<noteq> []"
by(auto simp add: red_external_list_def elim: is_external_call.cases)

lemma red_external_hext: "P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<Longrightarrow> hext h h'"
by(auto elim: red_external.cases)

lemma red_external_xcp_heap_unchanged:
  "P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>Inr xcp, h'\<rangle> \<Longrightarrow> h' = h"
by(auto elim: red_external.cases)

lemma red_external_list_xcp_heap_unchanged:
  "\<lbrakk> (ta, Inr xcp, h') \<in> set (red_external_list P a M vs h); is_external_call P (the (typeof\<^bsub>h\<^esub> (Addr a))) M \<rbrakk> \<Longrightarrow> h' = h"
unfolding red_external_list_def by(auto elim!: is_external_call.cases)

lemma red_ext_new_thread_heap:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t ex h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = h'"
by(auto elim: red_external.cases)

lemma red_ext_list_new_thread_heap:
  "\<lbrakk> (ta, va, h') \<in> set (red_external_list P a M vs h); is_external_call P (the (typeof\<^bsub>h\<^esub> (Addr a))) M; 
    NewThread t ex h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = h'"
by(auto simp add: red_external_list_def elim!: is_external_call.cases)

lemma red_external_new_thread_exists_thread_object:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; h a \<noteq> None \<rbrakk>
  \<Longrightarrow> \<exists>C fs. h' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
by(auto elim!: red_external.cases split: heapobj.split_asm dest!: Array_widen)

lemma red_external_list_new_thread_exists_thread_object:
  "\<lbrakk> (ta, va, h') \<in> set (red_external_list P a M vs h); is_external_call P (the (typeof\<^bsub>h\<^esub> (Addr a))) M;
     NewThread t x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; h a \<noteq> None \<rbrakk>
  \<Longrightarrow> \<exists>C fs. h' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
by(auto simp add: red_external_list_def elim!: is_external_call.cases split: heapobj.split_asm dest!: Array_widen)


subsection {* Typing of external calls *}

inductive external_WT :: "'m prog \<Rightarrow> ty \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> (_\<bullet>_'(_')) :: _" [50, 0, 0, 50] 60)
for P :: "'m prog"
where
  WTNewThread:
  "P \<turnstile> C \<preceq>\<^sup>* Thread \<Longrightarrow> P \<turnstile> Class C\<bullet>start([]) :: Void"

| WTWait:
  "\<lbrakk> is_refT T; T \<noteq> NT \<rbrakk> \<Longrightarrow> P \<turnstile> T\<bullet>wait([]) :: Void"

| WTNotify:
  "\<lbrakk> is_refT T; T \<noteq> NT \<rbrakk> \<Longrightarrow> P \<turnstile> T\<bullet>notify([]) :: Void"

| WTNotifyAll:
  "\<lbrakk> is_refT T; T \<noteq> NT \<rbrakk> \<Longrightarrow> P \<turnstile> T\<bullet>notifyAll([]) :: Void"

| WTJoin:
  "P \<turnstile> C \<preceq>\<^sup>* Thread \<Longrightarrow> P \<turnstile> Class C\<bullet>join([]) :: Void"

lemma external_WT_determ:
  "\<lbrakk> P \<turnstile> T\<bullet>M(Ts) :: U; P \<turnstile> T\<bullet>M(Ts) :: U' \<rbrakk> \<Longrightarrow> U = U'"
by(auto elim: external_WT.cases)

lemma external_WT_The_conv:
  "P \<turnstile> T\<bullet>M(TS) :: U \<Longrightarrow> (THE U. P \<turnstile> T\<bullet>M(TS) :: U) = U"
by(auto intro: external_WT_determ)

lemma external_WTrt_widen_mono:
  "\<lbrakk> P \<turnstile> T\<bullet>M(Ts) :: U; P \<turnstile> T' \<le> T; P \<turnstile> Ts' [\<le>] Ts; T' \<noteq> NT \<rbrakk> \<Longrightarrow> \<exists>U'. P \<turnstile> T'\<bullet>M(Ts') :: U' \<and> P \<turnstile> U' \<le> U"
by(fastsimp elim!: external_WT.cases intro: external_WT.intros simp add: widen_Class intro: rtranclp_trans widen_refT)

lemma external_WT_is_external_call:
  "P \<turnstile> T\<bullet>M(Ts) :: U \<Longrightarrow> is_external_call P T M"
by(auto elim!: external_WT.cases intro: is_external_call.intros)

lemma external_WT_not_NT:
  "P \<turnstile> T\<bullet>M(Ts) :: U \<Longrightarrow> T \<noteq> NT"
by(auto elim: external_WT.cases)

lemma WT_external_is_type:
  "\<lbrakk> P \<turnstile> T\<bullet>M(TS) :: U; is_type P T; set TS \<subseteq> is_type P \<rbrakk> \<Longrightarrow> is_type P U"
by(auto elim: external_WT.cases)

inductive external_WT' :: "'m prog \<Rightarrow> heap \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> (_\<bullet>_'(_')) : _" [50,0,0,0,50] 60)
for P :: "'m prog" and h :: heap and a :: addr and M :: mname and vs :: "val list" and U :: ty
where "\<lbrakk> typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>T\<rfloor>; map typeof\<^bsub>h\<^esub> vs = map Some Ts; P \<turnstile> T\<bullet>M(Ts) :: U \<rbrakk> \<Longrightarrow> P,h \<turnstile> a\<bullet>M(vs) : U"

lemma external_WT'_iff:
  "P,h \<turnstile> a\<bullet>M(vs) : U \<longleftrightarrow> (\<exists>T Ts. typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>T\<rfloor> \<and> map typeof\<^bsub>h\<^esub> vs = map Some Ts \<and> P \<turnstile> T\<bullet>M(Ts) :: U)"
by(auto simp add: external_WT'_def lfp_const)

lemma red_external_list_hext: "\<lbrakk> (ta, va, h') \<in> set (red_external_list P a M vs h); P,h \<turnstile> a\<bullet>M(vs) : U \<rbrakk> \<Longrightarrow> hext h h'"
by(auto simp add: red_external_list_def elim!: external_WT'.cases external_WT.cases)

lemma external_call_progress:
  "P,h \<turnstile> a\<bullet>M(vs) : U \<Longrightarrow> \<exists>ta va h'. P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
unfolding external_WT'_iff
by(fastsimp intro: red_external.intros simp del: split_paired_Ex split: heapobj.split_asm elim!: external_WT.cases)

lemma red_external_UnlockFail_UnlockFail: (* Used only in Compiler/Correctness1Threaded *)
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; UnlockFail \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l) \<rbrakk> \<Longrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l = [UnlockFail]"
by(auto elim: red_external.cases simp add: finfun_upd_apply split: split_if_asm)

subsection {* Lemmas for preservation of deadlocks *}

lemma red_external_Lock_hext:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l); hext h h'' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>M(vs), h''\<rangle> -ta\<rightarrow>ext \<langle>va, h''\<rangle>"
by(fastsimp elim!: red_external.cases intro: red_external.intros[simplified] simp add: finfun_upd_apply split: split_if_asm)

lemma red_external_Join_hext:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; hext h h''; h a \<noteq> None \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>M(vs), h''\<rangle> -ta\<rightarrow>ext \<langle>va, h''\<rangle>"
by(fastsimp elim!: red_external.cases intro: red_external.intros[simplified] dest: hext_objD Array_widen split: split_if_asm heapobj.split_asm)

lemma red_external_Lock_wth:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l); hext h'' h; P,h'' \<turnstile> a\<bullet>M(vs) : U \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>M(vs),h''\<rangle> -ta\<rightarrow>ext \<langle>va, h''\<rangle>"
by(auto elim!: red_external.cases intro: red_external.intros[simplified])

lemma red_external_Join_wth:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; hext h'' h; P,h'' \<turnstile> a\<bullet>M(vs) : U \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>a\<bullet>M(vs),h''\<rangle> -ta\<rightarrow>ext \<langle>va, h''\<rangle>"
by(fastsimp elim!: red_external.cases external_WT'.cases intro!: red_external.intros[simplified] dest: hext_objD hext_arrD split: heapobj.split_asm)

lemma red_external_wt_hconf_hext:
  "\<lbrakk> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; P,H \<turnstile> a\<bullet>M(vs) : U; hext H h \<rbrakk>
  \<Longrightarrow> \<exists>ta' va' h'. P \<turnstile> \<langle>a\<bullet>M(vs), H\<rangle> -ta'\<rightarrow>ext \<langle>va', h'\<rangle> \<and> locks_a ta' = locks_a ta \<and> wset_a ta' = wset_a ta \<and> cond_a ta' = cond_a ta"
by(fastsimp elim!: red_external.cases external_WT'.cases split: heapobj.splits dest: hext_objD hext_arrD intro: red_external.intros[simplified])

end