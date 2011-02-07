(*  Title:      JinjaThreads/Common/Observable_Events.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Observable events in JinjaThreads} *}

theory Observable_Events imports 
  Heap
  "../Framework/FWState"
begin

datatype obs_event =
    ExternalCall addr mname "val list" val
  | ReadMem addr addr_loc val
  | WriteMem addr addr_loc val
  | NewObj addr cname
  | NewArr addr ty nat
  | ThreadStart thread_id
  | ThreadJoin thread_id
  | SyncLock addr
  | SyncUnlock addr

types
  ('x, 'heap) Jinja_thread_action = "(addr,thread_id,'x,'heap,addr,obs_event list) thread_action"

translations
  (type) "('x, 'heap) Jinja_thread_action" <= (type) "(nat,nat,'x,'heap,nat,obs_event list) thread_action"

datatype htype =
  Class_type "cname"
| Array_type "ty" "nat"

primrec ty_of_htype :: "htype \<Rightarrow> ty"
where
  "ty_of_htype (Class_type C) = Class C"
| "ty_of_htype (Array_type T n) = Array T"

primrec NewHeapElem :: "addr \<Rightarrow> htype \<Rightarrow> obs_event"
where 
  "NewHeapElem ad (Class_type C) = NewObj ad C"
| "NewHeapElem ad (Array_type T n) = NewArr ad T n"

lemma NewHeapElem_simps [simp]:
  "NewHeapElem ad x = NewHeapElem ad' x' \<longleftrightarrow> ad = ad' \<and> x = x'"
  "NewHeapElem ad x = NewObj ad' C \<longleftrightarrow> ad = ad' \<and> x = Class_type C"
  "NewObj ad' C = NewHeapElem ad x \<longleftrightarrow> ad = ad' \<and> x = Class_type C"
  "NewHeapElem ad x = NewArr ad' T n \<longleftrightarrow> ad = ad' \<and> x = Array_type T n"
  "NewArr ad' T n = NewHeapElem ad x \<longleftrightarrow> ad = ad' \<and> x = Array_type T n"
  "NewHeapElem ad x \<noteq> ExternalCall ad' M vs v"
  "ExternalCall ad' M vs v \<noteq> NewHeapElem ad x"
  "NewHeapElem ad x \<noteq> ReadMem ad' al v"
  "ReadMem ad' al v \<noteq> NewHeapElem ad x"
  "NewHeapElem ad x \<noteq> WriteMem ad' al v"
  "WriteMem ad' al v \<noteq> NewHeapElem ad x"
  "NewHeapElem ad x \<noteq> ThreadStart t"
  "ThreadStart t \<noteq> NewHeapElem ad x"
  "NewHeapElem ad x \<noteq> ThreadJoin t"
  "ThreadJoin t \<noteq> NewHeapElem ad x"
  "NewHeapElem ad x \<noteq> SyncLock ad'"
  "SyncLock ad' \<noteq> NewHeapElem ad x"
  "NewHeapElem ad x \<noteq> SyncUnlock ad'"
  "SyncUnlock ad' \<noteq> NewHeapElem ad x"
apply(cases x')
apply(case_tac [!] x)
apply auto
done

context heap_base begin

inductive htypeof_addr :: "'heap \<Rightarrow> addr \<Rightarrow> htype \<Rightarrow> bool" ("_ \<turnstile>a _ : _" [50, 50, 50] 51)
for h :: 'heap and a :: addr
where
  Class_type: "typeof_addr h a = \<lfloor>Class C\<rfloor> \<Longrightarrow> h \<turnstile>a a : Class_type C"
| Array_type: "\<lbrakk> typeof_addr h a = \<lfloor>Array T\<rfloor>; n = array_length h a \<rbrakk> \<Longrightarrow> h \<turnstile>a a : Array_type T n"

inductive_simps htypeof_addr_simps [simp]:
  "h \<turnstile>a a : Class_type C"
  "h \<turnstile>a a : Array_type T n"

lemma htypeof_addr_hext_mono:
  "\<lbrakk> h \<unlhd> h'; h \<turnstile>a a : CTn \<rbrakk> \<Longrightarrow> h' \<turnstile>a a : CTn"
by(cases CTn)(auto dest: hext_objD hext_arrD)

end


lemma some_choice: "(\<exists>a. \<forall>b. P b (a b)) \<longleftrightarrow> (\<forall>b. \<exists>a. P b a)"
by metis


definition convert_RA :: "addr released_locks \<Rightarrow> obs_event list"
where "convert_RA ln = map SyncLock (finfun_to_list ln)"

lemma set_convert_RA_not_New [simp]:
  "NewObj a C \<notin> set (convert_RA ln)"
  "NewArr a T n \<notin> set (convert_RA ln)"
  "NewHeapElem a CTn \<notin> set (convert_RA ln)"
by(auto simp add: convert_RA_def)

lemma set_convert_RA_not_Read [simp]:
  "ReadMem ad al v \<notin> set (convert_RA ln)"
by(auto simp add: convert_RA_def)

end