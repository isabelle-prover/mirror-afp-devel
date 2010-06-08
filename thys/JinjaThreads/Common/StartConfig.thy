(*  Title:      JinjaThreads/Common/StartConfig.thy
    Author:     Andreas Lochbihler
*)

header {* 
  \isaheader{The initial configuration}
*}
theory StartConfig imports
  Exceptions
  Heap
  "../Framework/FWState"
begin

context heap_base begin

definition start_heap :: "'heap"
where
  "start_heap =
   (let (h0,  _) = new_obj empty_heap Thread;
        (h1,  _) = new_obj h0 NullPointer;
        (h2,  _) = new_obj h1 ClassCast;
        (h3,  _) = new_obj h2 OutOfMemory;
        (h4,  _) = new_obj h3 ArrayIndexOutOfBounds;
        (h5,  _) = new_obj h4 ArrayStore;
        (h6,  _) = new_obj h5 NegativeArraySize;
        (h7,  _) = new_obj h6 IllegalMonitorState;
        (h8,  _) = new_obj h7 IllegalThreadState;
        (h9,  _) = new_obj h8 CloneNotSupported;
        (h10, _) = new_obj h9 InterruptedException
    in h10)"

definition start_heap_ok :: bool
where 
  "start_heap_ok =
   (let (h0,  a0) = new_obj empty_heap Thread;
        (h1,  a1) = new_obj h0 NullPointer;
        (h2,  a2) = new_obj h1 ClassCast;
        (h3,  a3) = new_obj h2 OutOfMemory;
        (h4,  a4) = new_obj h3 ArrayIndexOutOfBounds;
        (h5,  a5) = new_obj h4 ArrayStore;
        (h6,  a6) = new_obj h5 NegativeArraySize;
        (h7,  a7) = new_obj h6 IllegalMonitorState;
        (h8,  a8) = new_obj h7 IllegalThreadState;
        (h9,  a9) = new_obj h8 CloneNotSupported;
        (h10, a10) = new_obj h9 InterruptedException
   in a0 \<noteq> None \<and> a1 \<noteq> None \<and> a2 \<noteq> None \<and> a3 \<noteq> None \<and> a4 \<noteq> None \<and> a5 \<noteq> None \<and>
      a6 \<noteq> None \<and> a7 \<noteq> None \<and> a8 \<noteq> None \<and> a9 \<noteq> None \<and> a10 \<noteq> None)"

definition start_tid :: addr
where 
  "start_tid =
  (let (_, ao) = new_obj empty_heap Thread
   in (the ao))"

definition addr_of_sys_xcpt :: "cname \<Rightarrow> addr"
where
  "addr_of_sys_xcpt C =
   (let (h0,  a0) = new_obj empty_heap Thread;
        (h1,  a1) = new_obj h0 NullPointer;
        (h2,  a2) = new_obj h1 ClassCast;
        (h3,  a3) = new_obj h2 OutOfMemory;
        (h4,  a4) = new_obj h3 ArrayIndexOutOfBounds;
        (h5,  a5) = new_obj h4 ArrayStore;
        (h6,  a6) = new_obj h5 NegativeArraySize;
        (h7,  a7) = new_obj h6 IllegalMonitorState;
        (h8,  a8) = new_obj h7 IllegalThreadState;
        (h9,  a9) = new_obj h8 CloneNotSupported;
        (h10, a10) = new_obj h9 InterruptedException

    in if C = NullPointer then the a1
       else if C = ClassCast then the a2
       else if C = OutOfMemory then the a3
       else if C = ArrayIndexOutOfBounds then the a4
       else if C = ArrayStore then the a5
       else if C = NegativeArraySize then the a6
       else if C = IllegalMonitorState then the a7
       else if C = IllegalThreadState then the a8
       else if C = CloneNotSupported then the a9
       else if C = InterruptedException then the a10
       else undefined)"

definition start_state :: "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'm \<Rightarrow> val list \<Rightarrow> 'x) \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> (addr,thread_id,'x,'heap,addr) state"
where
  "start_state f P C M vs \<equiv>
   let (D, Ts, T, m) = method P C M
   in (\<lambda>\<^isup>f None, ([start_tid \<mapsto> (f D M Ts T m vs, no_wait_locks)], start_heap), empty)"

subsection {* @{term preallocated} *}

definition preallocated :: "'heap \<Rightarrow> bool"
where "preallocated h \<equiv> \<forall>C \<in> sys_xcpts. typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class C\<rfloor>"

lemma typeof_addr_sys_xcp: 
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class C\<rfloor>"
by(simp add: preallocated_def)

lemma typeof_sys_xcp:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr (addr_of_sys_xcpt C)) = \<lfloor>Class C\<rfloor>"
by(simp add: typeof_addr_sys_xcp)

lemma [simp]:
  assumes "preallocated h"
  shows typeof_ClassCast: "typeof_addr h (addr_of_sys_xcpt ClassCast) = Some(Class ClassCast)"
  and typeof_OutOfMemory: "typeof_addr h (addr_of_sys_xcpt OutOfMemory) = Some(Class OutOfMemory)" 
  and typeof_NullPointer: "typeof_addr h (addr_of_sys_xcpt NullPointer) = Some(Class NullPointer)" 
  and typeof_ArrayIndexOutOfBounds: 
  "typeof_addr h (addr_of_sys_xcpt ArrayIndexOutOfBounds) = Some(Class ArrayIndexOutOfBounds)" 
  and typeof_ArrayStore: "typeof_addr h (addr_of_sys_xcpt ArrayStore) = Some(Class ArrayStore)" 
  and typeof_NegativeArraySize: "typeof_addr h (addr_of_sys_xcpt NegativeArraySize) = Some(Class NegativeArraySize)" 
  and typeof_IllegalMonitorState: "typeof_addr h (addr_of_sys_xcpt IllegalMonitorState) = Some(Class IllegalMonitorState)"
  and typeof_IllegalThreadState: "typeof_addr h (addr_of_sys_xcpt IllegalThreadState) = Some(Class IllegalThreadState)" 
  and typeof_CloneNotSupported: "typeof_addr h (addr_of_sys_xcpt CloneNotSupported) = Some(Class CloneNotSupported)" 
  and typeof_InterruptedException: "typeof_addr h (addr_of_sys_xcpt InterruptedException) = Some(Class InterruptedException)"
using assms
by(simp_all add: typeof_addr_sys_xcp)

lemma cname_of_xcp [simp]:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> cname_of h (addr_of_sys_xcpt C) = C"
by(drule (1) typeof_addr_sys_xcp)(simp add: cname_of_def)

lemma preallocated_hext:
  "\<lbrakk> preallocated h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> preallocated h'"
by (simp add: preallocated_def hext_def)

end

context heap begin

lemma preallocated_heap_ops:
  assumes "preallocated h"
  shows preallocated_new_obj: "\<And>a. new_obj h C = (h', a) \<Longrightarrow> preallocated h'"
  and preallocated_new_arr: "\<And>a. new_arr h T n = (h', a) \<Longrightarrow> preallocated h'"
  and preallocated_write_field: "heap_write h a al v h' \<Longrightarrow> preallocated h'"
using preallocated_hext[OF assms, of h']
by(blast intro: hext_heap_ops)+

lemma preallocated_start_heap:
  "start_heap_ok \<Longrightarrow> preallocated start_heap"
unfolding start_heap_ok_def preallocated_def start_heap_def
apply(clarsimp)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply clarsimp
apply(erule sys_xcpts_cases)
apply(simp_all add: addr_of_sys_xcpt_def sys_xcpts_neqs)
apply(assumption|erule typeof_addr_hext_mono)+
done

end

end