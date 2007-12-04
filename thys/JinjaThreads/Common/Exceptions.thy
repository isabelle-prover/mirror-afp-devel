(*  Title:      JinjaThreads/Common/Exceptions.thy
    Author:     Gerwin Klein, Martin Strecker, Andreas Lochbihler

    Based on the Jinja theory Common/Exceptions.thy by Gerwin Klein and Martin Strecker
*)

header {* \isaheader{Exceptions} *}

theory Exceptions imports Objects begin

constdefs
  NullPointer :: cname
  "NullPointer \<equiv> ''NullPointer''"

  ClassCast :: cname
  "ClassCast \<equiv> ''ClassCast''"

  OutOfMemory :: cname
  "OutOfMemory \<equiv> ''OutOfMemory''"

  ArrayIndexOutOfBounds :: cname
  "ArrayIndexOutOfBounds \<equiv> ''ArrayIndexOutOfBounds''"

  ArrayStore :: cname
  "ArrayStore \<equiv> ''ArrayStore''"

  NegativeArraySize :: cname
  "NegativeArraySize \<equiv> ''NegativeArraySize''"

  IllegalMonitorState :: cname
  "IllegalMonitorState \<equiv> ''IllegalMonitorState''"

  sys_xcpts :: "cname set"
  "sys_xcpts  \<equiv>  {NullPointer, ClassCast, OutOfMemory, ArrayIndexOutOfBounds, ArrayStore, NegativeArraySize, IllegalMonitorState}"

  addr_of_sys_xcpt :: "cname \<Rightarrow> addr"
  "addr_of_sys_xcpt s \<equiv> if s = NullPointer then 0 else
                        if s = ClassCast then 1 else
                        if s = OutOfMemory then 2 else
                        if s = ArrayIndexOutOfBounds then 3 else
                        if s = ArrayStore then 4 else
                        if s = NegativeArraySize then 5 else 
                        if s = IllegalMonitorState then 6 else arbitrary"

  start_heap :: "'c prog \<Rightarrow> heap"
  "start_heap G \<equiv> empty (addr_of_sys_xcpt NullPointer \<mapsto> blank G NullPointer)
                        (addr_of_sys_xcpt ClassCast \<mapsto> blank G ClassCast)
                        (addr_of_sys_xcpt OutOfMemory \<mapsto> blank G OutOfMemory)
                        (addr_of_sys_xcpt ArrayIndexOutOfBounds \<mapsto> blank G ArrayIndexOutOfBounds)
                        (addr_of_sys_xcpt ArrayStore \<mapsto> blank G ArrayStore)
                        (addr_of_sys_xcpt NegativeArraySize \<mapsto> blank G NegativeArraySize)
                        (addr_of_sys_xcpt IllegalMonitorState \<mapsto> blank G IllegalMonitorState)"

  preallocated :: "heap \<Rightarrow> bool"
  "preallocated h \<equiv> \<forall>C \<in> sys_xcpts. \<exists>fs. h(addr_of_sys_xcpt C) = Some (Obj C fs)"


section "System exceptions"

lemma [simp]:
  "NullPointer \<in> sys_xcpts \<and> 
   OutOfMemory \<in> sys_xcpts \<and> 
   ClassCast \<in> sys_xcpts \<and> 
   ArrayIndexOutOfBounds \<in> sys_xcpts \<and> 
   ArrayStore \<in> sys_xcpts \<and> 
   NegativeArraySize \<in> sys_xcpts \<and> 
   IllegalMonitorState \<in> sys_xcpts"
(*<*)by(simp add: sys_xcpts_def)(*>*)

lemma sys_xcpts_cases [consumes 1, cases set]:
  "\<lbrakk> C \<in> sys_xcpts; P NullPointer; P OutOfMemory; P ClassCast; P ArrayIndexOutOfBounds; P ArrayStore; P NegativeArraySize; P IllegalMonitorState \<rbrakk> \<Longrightarrow> P C"
(*<*)by (auto simp add: sys_xcpts_def)(*>*)

lemma OutOfMemory_not_Object[simp]: "OutOfMemory \<noteq> Object"
by(simp add: OutOfMemory_def Object_def)

lemma ClassCast_not_Object[simp]: "ClassCast \<noteq> Object"
by(simp add: ClassCast_def Object_def)

lemma NullPointer_not_Object[simp]: "NullPointer \<noteq> Object"
by(simp add: NullPointer_def Object_def)

lemma ArrayIndexOutOfBounds_not_Object[simp]: "ArrayIndexOutOfBounds \<noteq> Object"
by(simp add: ArrayIndexOutOfBounds_def Object_def)

lemma ArrayStore_not_Object[simp]: "ArrayStore \<noteq> Object"
by(simp add: ArrayStore_def Object_def)

lemma NegativeArraySize_not_Object[simp]: "NegativeArraySize \<noteq> Object"
by(simp add: NegativeArraySize_def Object_def)

lemma IllegalMonitorState_not_Object[simp]: "IllegalMonitorState \<noteq> Object"
by(simp add: IllegalMonitorState_def Object_def)

section "@{term preallocated}"

lemma preallocated_dom [simp]: 
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> addr_of_sys_xcpt C \<in> dom h"
(*<*)by (fastsimp simp:preallocated_def dom_def)(*>*)

lemma preallocatedD:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> \<exists>fs. h(addr_of_sys_xcpt C) = Some (Obj C fs)"
(*<*)by(auto simp add: preallocated_def sys_xcpts_def)(*>*)

lemma preallocatedE [elim?]:
  "\<lbrakk> preallocated h;  C \<in> sys_xcpts; \<And>fs. h(addr_of_sys_xcpt C) = Some (Obj C fs) \<Longrightarrow> P h C\<rbrakk>
  \<Longrightarrow> P h C"
(*<*)by (fast dest: preallocatedD)(*>*)

lemma cname_of_xcp [simp]:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> cname_of h (addr_of_sys_xcpt C) = C"
apply(erule preallocatedE)
apply(auto elim: preallocatedE)
done


lemma typeof_ClassCast [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt ClassCast)) = Some(Class ClassCast)" 
by(erule preallocatedE, auto split:heapobj.split if_splits simp add: addr_of_sys_xcpt_def preallocated_def)

lemma typeof_OutOfMemory [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt OutOfMemory)) = Some(Class OutOfMemory)" 
by(erule preallocatedE, auto split:heapobj.split if_splits simp add: addr_of_sys_xcpt_def preallocated_def)

lemma typeof_NullPointer [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NullPointer)) = Some(Class NullPointer)" 
by(erule preallocatedE, auto split:heapobj.split if_splits simp add: addr_of_sys_xcpt_def preallocated_def)

lemma typeof_ArrayIndexOutOfBounds [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt ArrayIndexOutOfBounds)) = Some(Class ArrayIndexOutOfBounds)" 
by(erule preallocatedE, auto split:heapobj.split if_splits simp add: addr_of_sys_xcpt_def preallocated_def)

lemma typeof_ArrayStore [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt ArrayStore)) = Some(Class ArrayStore)" 
by(erule preallocatedE, auto split:heapobj.split if_splits simp add: addr_of_sys_xcpt_def preallocated_def)

lemma typeof_NegativeArraySize [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NegativeArraySize)) = Some(Class NegativeArraySize)" 
by(erule preallocatedE, auto split:heapobj.split if_splits simp add: addr_of_sys_xcpt_def preallocated_def)

lemma typeof_IllegalMonitorState [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt IllegalMonitorState)) = Some(Class IllegalMonitorState)" 
by(erule preallocatedE, auto split:heapobj.split if_splits simp add: addr_of_sys_xcpt_def preallocated_def)

lemma preallocated_hext:
  "\<lbrakk> preallocated h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> preallocated h'"
(*<*)by (simp add: preallocated_def hext_def)(*>*)

(*<*)
lemmas preallocated_upd_obj = preallocated_hext [OF _ hext_upd_obj]
lemmas preallocated_upd_arr = preallocated_hext [OF _ hext_upd_arr]
lemmas preallocated_new  = preallocated_hext [OF _ hext_new]
(*>*)


lemma addrNullPointer: "addr_of_sys_xcpt NullPointer = 0"
by (simp add: addr_of_sys_xcpt_def)

lemma addrClassCast: "addr_of_sys_xcpt ClassCast = 1"
by (simp add: addr_of_sys_xcpt_def ClassCast_def NullPointer_def)

lemma addrOutOfMemory: "addr_of_sys_xcpt OutOfMemory = 2"
by (simp add: addr_of_sys_xcpt_def ClassCast_def NullPointer_def OutOfMemory_def)

lemma addrArrayIndex: "addr_of_sys_xcpt ArrayIndexOutOfBounds = 3"
by (simp add: addr_of_sys_xcpt_def ClassCast_def NullPointer_def OutOfMemory_def ArrayIndexOutOfBounds_def)

lemma addrArrayStore: "addr_of_sys_xcpt ArrayStore = 4"
by (simp add: addr_of_sys_xcpt_def ClassCast_def NullPointer_def OutOfMemory_def ArrayIndexOutOfBounds_def ArrayStore_def)

lemma addrNegativeArray: "addr_of_sys_xcpt NegativeArraySize = 5"
by (simp add: addr_of_sys_xcpt_def ClassCast_def NullPointer_def OutOfMemory_def ArrayIndexOutOfBounds_def ArrayStore_def NegativeArraySize_def)

lemma addrIllegalMonitorState: "addr_of_sys_xcpt IllegalMonitorState = 6"
by (simp add: addr_of_sys_xcpt_def ClassCast_def NullPointer_def OutOfMemory_def ArrayIndexOutOfBounds_def ArrayStore_def NegativeArraySize_def IllegalMonitorState_def)

lemma preallocated_start:
  "preallocated (start_heap P)"
apply(clarsimp simp add: preallocated_def)
apply(erule sys_xcpts_cases)
apply(simp, simp only: addrNullPointer addrClassCast addrOutOfMemory addrArrayIndex addrArrayStore addrNegativeArray addrIllegalMonitorState start_heap_def fun_upd_apply addr_of_sys_xcpt_def, simp only: NegativeArraySize_def NullPointer_def ClassCast_def OutOfMemory_def ArrayIndexOutOfBounds_def NegativeArraySize_def ArrayStore_def addrIllegalMonitorState, simp add: blank_def)+
done

end
