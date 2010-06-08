(*  Title:      JinjaThreads/Common/Heap.thy
    Author:     Andreas Lochbihler

    Reminiscent of the Jinja theory Common/Objects.thy
*)

header {* 
  \isaheader{An abstract heap model}
*}

theory Heap imports
  "../Common/Value"
begin

primrec typeof :: "val \<rightharpoonup> ty"
where
  "typeof  Unit    = Some Void"
| "typeof  Null    = Some NT"
| "typeof (Bool b) = Some Boolean"
| "typeof (Intg i) = Some Integer"
| "typeof (Addr a) = None"

datatype addr_loc =
    CField cname vname
  | ACell nat

locale heap_base =
  fixes empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
begin

fun typeof_h :: "'heap \<Rightarrow> val \<Rightarrow> ty option"  ("typeof\<^bsub>_\<^esub>")
where
  "typeof\<^bsub>h\<^esub> (Addr a) = typeof_addr h a"
| "typeof\<^bsub>h\<^esub>  v = typeof v"

definition cname_of :: "'heap \<Rightarrow> addr \<Rightarrow> cname"
where "cname_of h a = the_Class (the (typeof_addr h a))"

definition hext :: "'heap \<Rightarrow> 'heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
where
  "h \<unlhd> h' \<equiv> 
   (\<forall>a C. typeof_addr h a = \<lfloor>Class C\<rfloor> \<longrightarrow> typeof_addr h' a = \<lfloor>Class C\<rfloor>) \<and>
   (\<forall>a T. typeof_addr h a = \<lfloor>Array T\<rfloor> \<longrightarrow> typeof_addr h' a = \<lfloor>Array T\<rfloor> \<and> array_length h' a = array_length h a)"

inductive addr_loc_type :: "'m prog \<Rightarrow> 'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> ty \<Rightarrow> bool"
  ("_,_ \<turnstile> _@_ : _" [50, 50, 50, 50, 50] 51)
for P :: "'m prog" and h :: 'heap and a :: addr
where
  addr_loc_type_field:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class C\<rfloor>; P \<turnstile> C has F:T in D \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> a@CField D F : T"

| addr_loc_type_cell:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array T\<rfloor>; n < array_length h a \<rbrakk>
  \<Longrightarrow> P,h \<turnstile> a@ACell n : T"

definition typeof_addr_loc :: "'m prog \<Rightarrow> 'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> ty"
where "typeof_addr_loc P h a al = (THE T. P,h \<turnstile> a@al : T)"

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

lemma map_leI: -- "Move to Aux"
  "(\<And>k v. f k = Some v \<Longrightarrow> g k = Some v) \<Longrightarrow> f \<subseteq>\<^sub>m g"
unfolding map_le_def by auto

context heap_base begin

lemma hextI:
  "\<lbrakk> \<And>a C. typeof_addr h a = \<lfloor>Class C\<rfloor> \<Longrightarrow> typeof_addr h' a = \<lfloor>Class C\<rfloor>;
     \<And>a T. typeof_addr h a = \<lfloor>Array T\<rfloor> \<Longrightarrow> typeof_addr h' a = \<lfloor>Array T\<rfloor> \<and> array_length h' a = array_length h a \<rbrakk>
  \<Longrightarrow> h \<unlhd> h'"
unfolding hext_def by(auto)

lemma hext_objD: "\<lbrakk> h \<unlhd> h'; typeof_addr h a = \<lfloor>Class C\<rfloor> \<rbrakk> \<Longrightarrow> typeof_addr h' a = \<lfloor>Class C\<rfloor>"
unfolding hext_def by auto

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
apply (fastsimp dest: hext_arrD)
done

lemma typeof_lit_typeof:
  "typeof v = \<lfloor>T\<rfloor> \<Longrightarrow> typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>"
by(cases v)(simp_all)

lemma addr_loc_type_fun:
  "\<lbrakk> P,h \<turnstile> a@al : T; P,h \<turnstile> a@al : T' \<rbrakk> \<Longrightarrow> T = T'"
by(auto elim!: addr_loc_type.cases dest: has_field_fun)

lemma typeof_addr_locI [simp]:
  "P,h \<turnstile> a@al : T \<Longrightarrow> typeof_addr_loc P h a al = T"
by(auto simp add: typeof_addr_loc_def dest: addr_loc_type_fun)

end

locale heap =
  heap_base _ _ _ _ _ _ heap_write
  for heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool" +
  assumes empty_heap_empty [simp]:
  "typeof_addr empty_heap = empty"

  and new_obj_SomeD:
  "new_obj h C = (h', Some a)
  \<Longrightarrow> typeof_addr h a = None \<and> typeof_addr h' a = Some (Class C)"

  and hext_new_obj: "\<And>a. new_obj h C = (h', a) \<Longrightarrow> h \<unlhd> h'"

  and new_arr_SomeD:
  "new_arr h T n = (h', Some a)
  \<Longrightarrow> typeof_addr h a = None \<and> typeof_addr h' a = Some (T\<lfloor>\<rceil>) \<and> array_length h' a = n"

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
by(fastsimp elim!: addr_loc_type.cases intro: addr_loc_type.intros dest: hext_objD hext_arrD)

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

lemma empty_heap_hext [iff]: "empty_heap \<unlhd> h"
by(rule hextI)(simp_all add: empty_heap_empty)

end

end