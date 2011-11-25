(*  Title:      JinjaThreads/Common/Observable_Events.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Observable events in JinjaThreads} *}

theory Observable_Events
imports 
  Heap
  "../Framework/FWState"
begin

datatype ('addr,'thread_id) obs_event =
    ExternalCall 'addr mname "'addr val list" "'addr val"
  | ReadMem 'addr addr_loc "'addr val"
  | WriteMem 'addr addr_loc "'addr val"
  | NewObj 'addr cname
  | NewArr 'addr ty nat
  | ThreadStart 'thread_id
  | ThreadJoin 'thread_id
  | SyncLock 'addr
  | SyncUnlock 'addr
  | ObsInterrupt 'thread_id
  | ObsInterrupted 'thread_id

instance obs_event :: (type, type) obs_action
proof qed

type_synonym
  ('addr, 'thread_id, 'x, 'heap) Jinja_thread_action = 
    "('addr,'thread_id,'x,'heap,'addr,('addr, 'thread_id) obs_event) thread_action"

(* pretty printing for Jinja_thread_action type *)
print_translation {*
  let
    fun tr'
       [ a1, t1, x, h, a2
       , Const (@{type_syntax "obs_event"}, _) $ a3 $ t2] =
      if a1 = a2 andalso a2 = a3 andalso t1 = t2 then Syntax.const @{type_syntax "Jinja_thread_action"} $ a1 $ t1 $ x $ h
      else raise Match;
    in [(@{type_syntax "thread_action"}, tr')]
  end
*}
typ "('addr, 'thread_id, 'x, 'heap) Jinja_thread_action"

datatype htype =
  Class_type "cname"
| Array_type "ty" "nat"

primrec ty_of_htype :: "htype \<Rightarrow> ty"
where
  "ty_of_htype (Class_type C) = Class C"
| "ty_of_htype (Array_type T n) = Array T"

primrec alen_of_htype :: "htype \<Rightarrow> nat"
where
  "alen_of_htype (Array_type T n) = n"

primrec NewHeapElem :: "'addr \<Rightarrow> htype \<Rightarrow> ('addr, 'thread_id) obs_event"
where 
  "NewHeapElem ad (Class_type C) = NewObj ad C"
| "NewHeapElem ad (Array_type T n) = NewArr ad T n"

lemma range_ty_of_htype: "range ty_of_htype \<subseteq> range Class \<union> range Array"
apply(rule subsetI)
apply(erule rangeE)
apply(rename_tac ht)
apply(case_tac ht)
apply auto
done

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
  "NewHeapElem ad x \<noteq> ObsInterrupt t"
  "ObsInterrupt t \<noteq> NewHeapElem ad x"
  "NewHeapElem ad x \<noteq> ObsInterrupted t"
  "ObsInterrupted t \<noteq> NewHeapElem ad x"
apply(cases x')
apply(case_tac [!] x)
apply auto
done

context heap_base begin

inductive htypeof_addr :: "'heap \<Rightarrow> 'addr \<Rightarrow> htype \<Rightarrow> bool" ("_ \<turnstile>a _ : _" [50, 50, 50] 51)
for h :: 'heap and a :: 'addr
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

definition convert_RA :: "'addr released_locks \<Rightarrow> ('addr :: addr, 'thread_id) obs_event list"
where "convert_RA ln = concat (map (\<lambda>ad. replicate (ln\<^sub>f ad) (SyncLock ad)) (monitor_finfun_to_list ln))"

lemma set_convert_RA_not_New [simp]:
  "NewObj a C \<notin> set (convert_RA ln)"
  "NewArr a T n \<notin> set (convert_RA ln)"
  "NewHeapElem a CTn \<notin> set (convert_RA ln)"
by(auto simp add: convert_RA_def)

lemma set_convert_RA_not_Read [simp]:
  "ReadMem ad al v \<notin> set (convert_RA ln)"
by(auto simp add: convert_RA_def)

end