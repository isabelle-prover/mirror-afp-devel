(*  Title:      JinjaThreads/Common/Heap.thy
    Author:     Andreas Lochbihler

    Reminiscent of the Jinja theory Common/Objects.thy
*)

header {* 
  \isaheader{An abstract heap model}
*}

theory Heap
imports 
  Value
begin

primrec typeof :: "'addr val \<rightharpoonup> ty"
where
  "typeof  Unit    = Some Void"
| "typeof  Null    = Some NT"
| "typeof (Bool b) = Some Boolean"
| "typeof (Intg i) = Some Integer"
| "typeof (Addr a) = None"

datatype addr_loc =
    CField cname vname
  | ACell nat

lemma addr_loc_rec [simp]: "addr_loc_rec = addr_loc_case"
by(auto simp add: fun_eq_iff split: addr_loc.splits)

primrec is_volatile :: "'m prog \<Rightarrow> addr_loc \<Rightarrow> bool"
where 
  "is_volatile P (ACell n) = False"
| "is_volatile P (CField D F) = volatile (snd (snd (field P D F)))"

locale heap_base =
  addr_base addr2thread_id thread_id2addr 
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  +
  fixes empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
begin

fun typeof_h :: "'heap \<Rightarrow> 'addr val \<Rightarrow> ty option"  ("typeof\<^bsub>_\<^esub>")
where
  "typeof\<^bsub>h\<^esub> (Addr a) = typeof_addr h a"
| "typeof\<^bsub>h\<^esub>  v = typeof v"

definition cname_of :: "'heap \<Rightarrow> 'addr \<Rightarrow> cname"
where "cname_of h a = the_Class (the (typeof_addr h a))"

definition hext :: "'heap \<Rightarrow> 'heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
where
  "h \<unlhd> h' \<equiv> 
   (\<forall>a C. typeof_addr h a = \<lfloor>Class C\<rfloor> \<longrightarrow> typeof_addr h' a = \<lfloor>Class C\<rfloor>) \<and>
   (\<forall>a T. typeof_addr h a = \<lfloor>Array T\<rfloor> \<longrightarrow> typeof_addr h' a = \<lfloor>Array T\<rfloor> \<and> array_length h' a = array_length h a)"

inductive addr_loc_type :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> ty \<Rightarrow> bool"
  ("_,_ \<turnstile> _@_ : _" [50, 50, 50, 50, 50] 51)
for P :: "'m prog" and h :: 'heap and a :: 'addr
where
  addr_loc_type_field:
  "\<lbrakk> typeof_addr h a = \<lfloor>U\<rfloor>; is_class_type_of U C; P \<turnstile> C has F:T (fm) in D \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> a@CField D F : T"

| addr_loc_type_cell:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array T\<rfloor>; n < array_length h a \<rbrakk>
  \<Longrightarrow> P,h \<turnstile> a@ACell n : T"

definition typeof_addr_loc :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> ty"
where "typeof_addr_loc P h a al = (THE T. P,h \<turnstile> a@al : T)"

definition deterministic_heap_ops :: bool
where
  "deterministic_heap_ops \<longleftrightarrow>
  (\<forall>h ad al v v'. heap_read h ad al v \<longrightarrow> heap_read h ad al v' \<longrightarrow> v = v') \<and>
  (\<forall>h ad al v h' h''. heap_write h ad al v h' \<longrightarrow> heap_write h ad al v h'' \<longrightarrow> h' = h'')"

end

lemma typeof_lit_eq_Boolean [simp]: "(typeof v = Some Boolean) = (\<exists>b. v = Bool b)"
by(cases v)(auto)

lemma typeof_lit_eq_Integer [simp]: "(typeof v = Some Integer) = (\<exists>i. v = Intg i)"
by(cases v)(auto)

lemma typeof_lit_eq_NT [simp]: "(typeof v = Some NT) = (v = Null)"
by(cases v)(auto)

lemma typeof_lit_eq_Void [simp]: "typeof v = Some Void \<longleftrightarrow> v = Unit"
by(cases v)(auto)

lemma typeof_lit_neq_Class [simp]: "typeof v \<noteq> Some (Class C)"
by(cases v) auto

lemma typeof_lit_neq_Array [simp]: "typeof v \<noteq> Some (Array T)"
by(cases v) auto

lemma typeof_NoneD [simp,dest]:
  "typeof v = Some x \<Longrightarrow> \<not> is_Addr v"
  by (cases v) auto

lemma typeof_lit_is_type:
  "typeof v = Some T \<Longrightarrow> is_type P T"
by(cases v) auto

context heap_base begin

lemma hextI:
  "\<lbrakk> \<And>a C. typeof_addr h a = \<lfloor>Class C\<rfloor> \<Longrightarrow> typeof_addr h' a = \<lfloor>Class C\<rfloor>;
     \<And>a T. typeof_addr h a = \<lfloor>Array T\<rfloor> \<Longrightarrow> typeof_addr h' a = \<lfloor>Array T\<rfloor> \<and> array_length h' a = array_length h a \<rbrakk>
  \<Longrightarrow> h \<unlhd> h'"
unfolding hext_def by(auto)

lemma hext_objD:
  assumes "h \<unlhd> h'"
  and "typeof_addr h a = \<lfloor>Class C\<rfloor>"
  shows "typeof_addr h' a = \<lfloor>Class C\<rfloor>"
using assms unfolding hext_def by auto

lemma hext_arrD:
  assumes "h \<unlhd> h'" "typeof_addr h a = \<lfloor>Array T\<rfloor>"
  shows "typeof_addr h' a = \<lfloor>Array T\<rfloor>"
  and "array_length h' a = array_length h a"
using assms unfolding hext_def by blast+

lemma hext_refl [iff]: "h \<unlhd> h"
by (rule hextI) blast+

lemma hext_trans [trans]: "\<lbrakk> h \<unlhd> h'; h' \<unlhd> h'' \<rbrakk> \<Longrightarrow> h \<unlhd> h''"
apply (rule hextI)
apply (fast dest: hext_objD)
apply (fastforce dest: hext_arrD)
done

lemma typeof_lit_typeof:
  "typeof v = \<lfloor>T\<rfloor> \<Longrightarrow> typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>"
by(cases v)(simp_all)

lemma addr_loc_type_fun:
  "\<lbrakk> P,h \<turnstile> a@al : T; P,h \<turnstile> a@al : T' \<rbrakk> \<Longrightarrow> T = T'"
by(auto elim!: addr_loc_type.cases dest: has_field_fun simp add: is_class_type_of_conv_class_type_of_Some)

lemma typeof_addr_locI [simp]:
  "P,h \<turnstile> a@al : T \<Longrightarrow> typeof_addr_loc P h a al = T"
by(auto simp add: typeof_addr_loc_def dest: addr_loc_type_fun)

lemma deterministic_heap_opsI:
  "\<lbrakk> \<And>h ad al v v'. \<lbrakk> heap_read h ad al v; heap_read h ad al v' \<rbrakk> \<Longrightarrow> v = v';
     \<And>h ad al v h' h''. \<lbrakk> heap_write h ad al v h'; heap_write h ad al v h'' \<rbrakk> \<Longrightarrow> h' = h''\<rbrakk>
  \<Longrightarrow> deterministic_heap_ops"
unfolding deterministic_heap_ops_def by blast

lemma deterministic_heap_ops_readD:
  "\<lbrakk> deterministic_heap_ops; heap_read h ad al v; heap_read h ad al v' \<rbrakk> \<Longrightarrow> v = v'"
unfolding deterministic_heap_ops_def by blast

lemma deterministic_heap_ops_writeD:
  "\<lbrakk> deterministic_heap_ops; heap_write h ad al v h'; heap_write h ad al v h'' \<rbrakk> \<Longrightarrow> h' = h''"
unfolding deterministic_heap_ops_def by blast

end

locale addr_conv =
  heap_base
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
  +
  prog P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'m prog"
  +
  assumes addr2thread_id_inverse: 
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> thread_id2addr (addr2thread_id a) = a"
begin

lemma typeof_addr_thread_id2_addr_addr2thread_id [simp]:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> typeof_addr h (thread_id2addr (addr2thread_id a)) = \<lfloor>Class C\<rfloor>"
by(simp add: addr2thread_id_inverse)

end

locale heap =
  addr_conv
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'m prog"
  +
  assumes new_obj_SomeD:
  "\<lbrakk> new_obj h C = (h', Some a); is_class P C \<rbrakk> \<Longrightarrow> typeof_addr h' a = Some (Class C)"

  and hext_new_obj: "\<And>a. new_obj h C = (h', a) \<Longrightarrow> h \<unlhd> h'"

  and new_arr_SomeD:
  "\<lbrakk> new_arr h T n = (h', Some a); is_type P (T\<lfloor>\<rceil>) \<rbrakk>
  \<Longrightarrow> typeof_addr h' a = Some (T\<lfloor>\<rceil>) \<and> array_length h' a = n"

  and hext_new_arr: "\<And>a. new_arr h T n = (h', a) \<Longrightarrow> h \<unlhd> h'"

  and ran_typeof_addr:
  "ran (typeof_addr h) \<subseteq> range Class \<union> range Array"

  and hext_heap_write:
  "heap_write h a al v h' \<Longrightarrow> h \<unlhd> h'"

begin

lemmas hext_heap_ops = 
  hext_new_obj hext_new_arr
  hext_heap_write

lemma hext_heap_ops_mono':
  shows hext_new_obj': "h \<unlhd> fst (new_obj h C)"
  and hext_new_arr': "h \<unlhd> fst (new_arr h T n)"
using hext_new_obj[of h C "fst (new_obj h C)" "snd (new_obj h C)"]
  and hext_new_arr[of h T n "fst (new_arr h T n)" "snd (new_arr h T n)"]
by auto

lemma typeof_addr_eq_Some_conv:
  "typeof_addr h a = Some T \<Longrightarrow> (\<exists>C. T = Class C) \<or> (\<exists>U. T = U\<lfloor>\<rceil>)"
using ran_typeof_addr[of h] unfolding ran_def by auto

lemma typeof_h_eq_Boolean [simp]: "(typeof\<^bsub>h\<^esub> v = Some Boolean) = (\<exists>b. v = Bool b)"
by(cases v)(auto dest: typeof_addr_eq_Some_conv)

lemma typeof_h_eq_Integer [simp]: "(typeof\<^bsub>h\<^esub> v = Some Integer) = (\<exists>i. v = Intg i)"
by(cases v)(auto dest: typeof_addr_eq_Some_conv)

lemma typeof_h_eq_NT [simp]: "(typeof\<^bsub>h\<^esub> v = Some NT) = (v = Null)"
by(cases v)(auto dest: typeof_addr_eq_Some_conv)

lemma typeof_addr_hext_mono:
  "\<lbrakk> h \<unlhd> h'; typeof_addr h a = \<lfloor>T\<rfloor> \<rbrakk> \<Longrightarrow> typeof_addr h' a = \<lfloor>T\<rfloor>"
using ran_typeof_addr[of h] unfolding ran_def
by(auto dest: typeof_addr_eq_Some_conv hext_objD hext_arrD)

lemma hext_typeof_mono:
  "\<lbrakk> h \<unlhd> h'; typeof\<^bsub>h\<^esub> v = Some T \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> v = Some T"
by (cases v)(auto intro: typeof_addr_hext_mono)

lemma addr_loc_type_hext_mono:
  "\<lbrakk> P,h \<turnstile> a@al : T; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> a@al : T"
by(force elim!: addr_loc_type.cases intro: addr_loc_type.intros elim: typeof_addr_hext_mono dest: hext_arrD)

lemma type_of_hext_type_of: -- "FIXME: What's this rule good for?"
  "\<lbrakk> typeof\<^bsub>h\<^esub> w = \<lfloor>T\<rfloor>; hext h h' \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> w = \<lfloor>T\<rfloor>"
by(rule hext_typeof_mono)

lemma hext_None: "\<lbrakk> h \<unlhd> h'; typeof_addr h' a = None \<rbrakk> \<Longrightarrow> typeof_addr h a = None"
by(rule ccontr)(auto dest: typeof_addr_hext_mono)

lemma map_typeof_hext_mono:
  "\<lbrakk> map typeof\<^bsub>h\<^esub> vs = map Some Ts; h \<unlhd> h' \<rbrakk> \<Longrightarrow>  map typeof\<^bsub>h'\<^esub> vs = map Some Ts"
apply(induct vs arbitrary: Ts)
apply(auto simp add: Cons_eq_map_conv intro: hext_typeof_mono)
done

lemma hext_typeof_addr_map_le:
  "h \<unlhd> h' \<Longrightarrow> typeof_addr h \<subseteq>\<^sub>m typeof_addr h'"
by(auto simp add: map_le_def dest: typeof_addr_hext_mono)

lemma hext_dom_typeof_addr_subset:
  "h \<unlhd> h' \<Longrightarrow> dom (typeof_addr h) \<subseteq> dom (typeof_addr h')"
by (metis hext_typeof_addr_map_le map_le_implies_dom_le)

end

declare heap_base.typeof_h.simps [code]
declare heap_base.cname_of_def [code]

end