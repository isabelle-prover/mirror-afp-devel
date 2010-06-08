(*  Title:      JinjaThreads/MM/SC.thy
    Author:     David von Oheimb, Andreas Lochbihler

    Based on the Jinja theories Common/Objects.thy and Common/Conform by David von Oheimb
*)

header {* \chapter{Memory Models}
          \isaheader{The heap implemented as a map} *}

theory SC imports 
  "../Common/Conform"
begin

subsection{* Objects and Arrays *}

types 
  fields = "vname \<times> cname \<rightharpoonup> val"       -- "field name, defining class, value"

datatype heapobj
  = Obj cname fields                    -- "class instance with class name and fields"
  | Arr ty "val list"                   -- "element type and list of each cell's content"

lemma heapobj_rec [simp]: "heapobj_rec = heapobj_case"
by(auto intro!: ext split: heapobj.split)

primrec obj_ty  :: "heapobj \<Rightarrow> ty"
where
  "obj_ty (Obj c f)   = Class c"
| "obj_ty (Arr t e) = Array t"

fun is_Arr :: "heapobj \<Rightarrow> bool" where
  "is_Arr (Obj C fs)    = False"
| "is_Arr (Arr T el) = True"

lemma is_Arr_conv:
  "is_Arr arrobj = (\<exists>T el. arrobj = Arr T el)"
by(cases arrobj, auto)

lemma is_ArrE:
  "\<lbrakk> is_Arr arrobj; \<And>T el. arrobj = Arr T el \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
  "\<lbrakk> \<not> is_Arr arrobj; \<And>C fs. arrobj = Obj C fs \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(cases arrobj, auto)+

definition init_fields :: "((vname \<times> cname) \<times> ty) list \<Rightarrow> fields"
where "init_fields  \<equiv>  map_of \<circ> map (\<lambda>(F,T). (F,default_val T))"
  
definition
  -- "a new, blank object with default values in all fields:"
  blank :: "'m prog \<Rightarrow> cname \<Rightarrow> heapobj"
where
  "blank P C  \<equiv>  Obj C (init_fields (fields P C))"

lemma blank_obj: "\<exists>c f. blank P C = Obj c f"
by(simp add: blank_def)

lemma obj_ty_blank [iff]: "obj_ty (blank P C) = Class C"
  by (simp add: blank_def)

subsection{* Heap *}

types heap = "addr \<rightharpoonup> heapobj"

translations
  (type) "heap" <= (type) "nat \<Rightarrow> heapobj option"

fun the_obj :: "heapobj \<Rightarrow> cname \<times> fields" where
  "the_obj (Obj C fs) = (C, fs)"

fun the_arr :: "heapobj \<Rightarrow> ty \<times> val list" where
  "the_arr (Arr T el) = (T, el)"


abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the_obj (the (hp a)))"

definition new_Addr  :: "heap \<Rightarrow> addr option"
where "new_Addr h  \<equiv>  if \<exists>a. h a = None then Some(SOME a. h a = None) else None"

definition sc_new_obj :: "'m prog \<Rightarrow> heap \<Rightarrow> cname \<Rightarrow> (heap \<times> addr option)"
where
  "sc_new_obj P h C = 
   (case new_Addr h of None \<Rightarrow> (h, None)
                   | Some a \<Rightarrow> (h(a \<mapsto> blank P C), Some a))"

definition sc_new_arr :: "heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> (heap \<times> addr option)"
where
  "sc_new_arr h T n =
  (case new_Addr h of None \<Rightarrow> (h, None)
                  | Some a \<Rightarrow> (h(a \<mapsto> Arr T (replicate n (default_val T))), Some a))"

definition sc_typeof_addr :: "heap \<Rightarrow> addr \<Rightarrow> ty option"
where "sc_typeof_addr h a = Option.map obj_ty (h a)"

definition sc_array_length :: "heap \<Rightarrow> addr \<Rightarrow> nat"
where "sc_array_length h a = (case the (h a) of Arr T el \<Rightarrow> length el | _ \<Rightarrow> undefined)"

inductive sc_heap_read :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
for h :: heap and a :: addr
where
  Obj: "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; fs (F, D) = \<lfloor>v\<rfloor> \<rbrakk> \<Longrightarrow> sc_heap_read h a (CField D F) v"
| Arr: "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; n < length el \<rbrakk> \<Longrightarrow> sc_heap_read h a (ACell n) (el ! n)"

hide_fact (open) Obj Arr

inductive_cases sc_heap_read_cases [elim!]:
  "sc_heap_read h a (CField C F) v"
  "sc_heap_read h a (ACell n) v"

inductive sc_heap_write :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> heap \<Rightarrow> bool"
for h :: heap and a :: addr
where
  Obj: "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; h' = h(a \<mapsto> Obj C (fs((F, D) \<mapsto> v))) \<rbrakk> \<Longrightarrow> sc_heap_write h a (CField D F) v h'"
| Arr: "\<lbrakk> h a = \<lfloor>Arr T el\<rfloor>; h' = h(a \<mapsto> Arr T (el[n := v])) \<rbrakk> \<Longrightarrow> sc_heap_write h a (ACell n) v h'"

hide_fact (open) Obj Arr

inductive_cases sc_heap_write_cases [elim!]:
  "sc_heap_write h a (CField C F) v h'"
  "sc_heap_write h a (ACell n) v h'"

interpretation sc!: heap_base
  "empty"
  "sc_new_obj P"
  "sc_new_arr" 
  "sc_typeof_addr"
  "sc_array_length"
  "sc_heap_read"
  "sc_heap_write"
for P
.

(* FIXME! Why does sc.preallocated need the type token?? *)
abbreviation sc_preallocated :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"
where "sc_preallocated == sc.preallocated TYPE('m)"


text {* Translate notation from @{text heap_base} *}

notation sc.hext ("_ \<unlhd>sc _" [51,51] 50)
notation sc.conf ("_,_ \<turnstile>sc _ :\<le> _"  [51,51,51,51] 50)

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
by(fastsimp simp add:new_Addr_def split:if_splits intro:someI)

lemma sc_heap: "heap empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_write"
proof
  show "sc_typeof_addr empty = empty"
    by(auto simp add: sc_typeof_addr_def intro: ext)
next
  fix h C h' a
  assume "sc_new_obj P h C = (h', \<lfloor>a\<rfloor>)"
  thus "sc_typeof_addr h a = None \<and> sc_typeof_addr h' a = \<lfloor>Class C\<rfloor>"
    by(auto simp add: sc_new_obj_def sc_typeof_addr_def dest: new_Addr_SomeD split: split_if_asm)
next
  fix h C h' a
  assume "sc_new_obj P h C = (h', a)"
  thus "h \<unlhd>sc h'"
    by(force simp add: sc_new_obj_def sc_typeof_addr_def sc_array_length_def intro!: sc.hextI dest: new_Addr_SomeD[OF sym] split: heapobj.split split_if_asm)
next
  fix h T n h' a
  assume "sc_new_arr h T n = (h', \<lfloor>a\<rfloor>)"
  thus "sc_typeof_addr h a = None \<and> sc_typeof_addr h' a = \<lfloor>T\<lfloor>\<rceil>\<rfloor> \<and> sc_array_length h' a = n"
    by(auto simp add: sc_new_arr_def sc_typeof_addr_def sc_array_length_def intro: new_Addr_SomeD split: split_if_asm)
next
  fix h T n h' a
  assume "sc_new_arr h T n = (h', a)"
  thus "h \<unlhd>sc h'"
    by(force intro!: sc.hextI simp add: sc_typeof_addr_def sc_new_arr_def sc_array_length_def dest: new_Addr_SomeD[OF sym] split: split_if_asm)
next
  fix h
  show "ran (sc_typeof_addr h) \<subseteq> range Class \<union> range Array"
    apply(auto simp add: ran_def sc_typeof_addr_def)
    apply(case_tac z)
    apply auto
    done
next
  fix h a al v h'
  assume "sc_heap_write h a al v h'"
  thus "h \<unlhd>sc h'"
    by(cases al)(auto intro!: sc.hextI simp add: sc_typeof_addr_def sc_array_length_def)
qed

interpretation sc!: heap 
  "empty"
  "sc_new_obj P"
  "sc_new_arr" 
  "sc_typeof_addr"
  "sc_array_length"
  "sc_heap_read"
  "sc_heap_write"
for P
by(rule sc_heap)

lemma sc_hext_new:
  "h a = None \<Longrightarrow> h \<unlhd>sc h(a \<mapsto> arrobj)"
by(rule sc.hextI)(auto simp add: sc_typeof_addr_def sc_array_length_def dest!: new_Addr_SomeD)

lemma sc_hext_upd_obj: "h a = Some (Obj C fs) \<Longrightarrow> h \<unlhd>sc h(a\<mapsto>(Obj C fs'))"
by (rule sc.hextI) (auto simp:fun_upd_apply sc_typeof_addr_def sc_array_length_def)

lemma sc_hext_upd_arr: "\<lbrakk> h a = Some (Arr T e); length e = length e' \<rbrakk> \<Longrightarrow> h \<unlhd>sc h(a\<mapsto>(Arr T e'))"
by(rule sc.hextI) (auto simp:fun_upd_apply sc_typeof_addr_def sc_array_length_def)

subsection {* Conformance *}

definition sc_oconf :: "'m prog \<Rightarrow> heap \<Rightarrow> heapobj \<Rightarrow> bool"   ("_,_ \<turnstile>sc _ \<surd>" [51,51,51] 50)
where
  "P,h \<turnstile>sc obj \<surd>  \<equiv>
   (case obj of Obj C fs \<Rightarrow> is_class P C \<and> (\<forall>F D T. P \<turnstile> C has F:T in D \<longrightarrow> (\<exists>v. fs(F,D) = Some v \<and> P,h \<turnstile>sc v :\<le> T))
              | Arr T el \<Rightarrow> is_type P T \<and> (\<forall>v \<in> set el. P,h \<turnstile>sc v :\<le> T))"


definition sc_hconf :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"  ("_ \<turnstile>sc _ \<surd>" [51,51] 50)
where "P \<turnstile>sc h \<surd> \<longleftrightarrow> (\<forall>a obj. h a = Some obj \<longrightarrow> P,h \<turnstile>sc obj \<surd>)"

interpretation sc!: heap_conf_base  
  "empty"
  "sc_new_obj P"
  "sc_new_arr" 
  "sc_typeof_addr"
  "sc_array_length"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P
.

lemma sc_conf_upd_obj: "h a = Some(Obj C fs) \<Longrightarrow> (P,h(a\<mapsto>(Obj C fs')) \<turnstile>sc x :\<le> T) = (P,h \<turnstile>sc x :\<le> T)"
apply (unfold sc.conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
apply (auto simp add: sc_typeof_addr_def split: split_if_asm)
done

lemma sc_conf_upd_arr: "h a = Some(Arr T el) \<Longrightarrow> (P,h(a\<mapsto>(Arr T el')) \<turnstile>sc x :\<le> T') = (P,h \<turnstile>sc x :\<le> T')"
apply(unfold sc.conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
apply(auto simp add: sc_typeof_addr_def split: split_if_asm)
done

lemma sc_oconf_hext: "P,h \<turnstile>sc obj \<surd> \<Longrightarrow> h \<unlhd>sc h' \<Longrightarrow> P,h' \<turnstile>sc obj \<surd>"
unfolding sc_oconf_def
by(fastsimp split: heapobj.split elim: sc.conf_hext)

lemma sc_oconf_init_fields:
  assumes "P \<turnstile> C has_fields FDTs"
  shows "P,h \<turnstile>sc (Obj C (init_fields FDTs)) \<surd>"
using assms has_fields_is_class[OF assms]
by(fastsimp simp add: has_field_def sc_oconf_def init_fields_def map_of_map
            dest: has_fields_fun)

lemma sc_oconf_init_arr:
 "is_type P U \<Longrightarrow> P,h \<turnstile>sc (Arr U (replicate n (default_val U))) \<surd>"
by(simp add: sc_oconf_def set_replicate_conv_if)

lemma sc_oconf_fupd [intro?]:
  "\<lbrakk> P \<turnstile> C has F:T in D; P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Obj C fs) \<surd> \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile>sc (Obj C (fs((F,D)\<mapsto>v))) \<surd>"
unfolding sc_oconf_def has_field_def
by(fastsimp dest: has_fields_fun simp add: fun_upd_apply)

lemma sc_oconf_fupd_arr [intro?]:
  "\<lbrakk> P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Arr T el) \<surd> \<rbrakk>
  \<Longrightarrow> P,h \<turnstile>sc (Arr T (el[i := v])) \<surd>"
unfolding sc_oconf_def
by(auto dest: subsetD[OF set_update_subset_insert])

lemma sc_oconf_new: "\<lbrakk> P,h \<turnstile>sc obj \<surd>; h a = None \<rbrakk> \<Longrightarrow> P,h(a \<mapsto> arrobj) \<turnstile>sc obj \<surd>"
by(erule sc_oconf_hext)(rule sc_hext_new)

lemma sc_oconf_blank: "is_class P C \<Longrightarrow> P,h \<turnstile>sc blank P C \<surd>"
by(auto simp add: sc_oconf_def blank_def init_fields_def has_field_def map_of_map)

lemmas sc_oconf_upd_obj = sc_oconf_hext [OF _ sc_hext_upd_obj]

lemma sc_oconf_upd_arr:
  "\<lbrakk> P,h \<turnstile>sc obj \<surd>; h a = \<lfloor>Arr T el\<rfloor> \<rbrakk> \<Longrightarrow> P,h(a \<mapsto> Arr T el') \<turnstile>sc obj \<surd>"
by(auto simp add: sc_oconf_def sc_conf_upd_arr split: heapobj.split)

lemma sc_hconfD: "\<lbrakk> P \<turnstile>sc h \<surd>; h a = Some obj \<rbrakk> \<Longrightarrow> P,h \<turnstile>sc obj \<surd>"
unfolding sc_hconf_def by blast

lemmas sc_preallocated_new = sc.preallocated_hext[OF _ sc_hext_new]
lemmas sc_preallocated_upd_obj = sc.preallocated_hext [OF _ sc_hext_upd_obj]
lemmas sc_preallocated_upd_arr = sc.preallocated_hext [OF _ sc_hext_upd_arr]

lemma sc_hconf_new: "\<lbrakk> P \<turnstile>sc h \<surd>; h a = None; P,h \<turnstile>sc obj \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc h(a\<mapsto>obj) \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_new)

lemma sc_hconf_upd_obj: "\<lbrakk> P \<turnstile>sc h \<surd>; h a = Some (Obj C fs); P,h \<turnstile>sc (Obj C fs') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc h(a\<mapsto>(Obj C fs')) \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_upd_obj)

lemma sc_hconf_upd_arr: "\<lbrakk> P \<turnstile>sc h \<surd>; h a = Some(Arr T el); P,h \<turnstile>sc (Arr T el') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc h(a\<mapsto>(Arr T el')) \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_upd_arr)

lemma sc_heap_conf: "heap_conf empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_write (sc_hconf P) P"
proof
  show "P \<turnstile>sc Map.empty \<surd>" by(simp add: sc_hconf_def)
next
  fix h a T
  assume "sc_typeof_addr h a = \<lfloor>T\<rfloor>" "P \<turnstile>sc h \<surd>"
  thus "is_type P T"
    by(auto simp add: sc_typeof_addr_def sc_oconf_def dest!: sc_hconfD split: heapobj.split_asm)
next
  fix h C h' a
  assume "P \<turnstile>sc h \<surd>" "sc_new_obj P h C = (h', a)" "is_class P C"
  thus "P \<turnstile>sc h' \<surd>"
    by(auto simp add: sc_new_obj_def dest!: new_Addr_SomeD[OF sym] intro: sc_hconf_new sc_oconf_blank split: split_if_asm)
next
  fix h T n h' a
  assume "P \<turnstile>sc h \<surd>" "sc_new_arr h T n = (h', a)" "is_type P T"
  thus "P \<turnstile>sc h' \<surd>"
    by(auto simp add: sc_new_arr_def dest!: new_Addr_SomeD[OF sym] intro: sc_hconf_new sc_oconf_init_arr split: split_if_asm)
next
  fix h a al T v h'
  assume "P \<turnstile>sc h \<surd>"
    and "sc.addr_loc_type P h a al T"
    and "P,h \<turnstile>sc v :\<le> T"
    and "sc_heap_write h a al v h'"
  thus "P \<turnstile>sc h' \<surd>"
    by(cases al)(fastsimp elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def intro: sc_hconf_upd_obj sc_oconf_fupd sc_hconfD sc_hconf_upd_arr sc_oconf_fupd_arr)+
qed

interpretation sc!: heap_conf
  "empty"
  "sc_new_obj P"
  "sc_new_arr" 
  "sc_typeof_addr"
  "sc_array_length"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P
by(rule sc_heap_conf)

lemma sc_heap_progress:
  "heap_progress empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_read sc_heap_write (sc_hconf P) P"
proof
  fix h a al T
  assume hconf: "P \<turnstile>sc h \<surd>"
    and alt: "sc.addr_loc_type P h a al T"
  from alt obtain arrobj where arrobj: "h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
  show "\<exists>v. sc_heap_read h a al v \<and> P,h \<turnstile>sc v :\<le> T"
  proof(cases arrobj)
    case (Obj C fs)
    with alt arrobj obtain D F 
      where [simp]: "al = CField D F"
      and "P \<turnstile> C has F:T in D"
      by(fastsimp elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
    from hconf arrobj Obj have "P,h \<turnstile>sc Obj C fs \<surd>" by(auto dest: sc_hconfD)
    with `P \<turnstile> C has F:T in D` obtain v 
      where "fs (F, D) = \<lfloor>v\<rfloor>" "P,h \<turnstile>sc v :\<le> T" by(fastsimp simp add: sc_oconf_def)
    thus ?thesis using Obj arrobj by(auto intro: sc_heap_read.intros)
  next
    case (Arr T' el)
    with alt arrobj obtain n 
      where [simp]: "al = ACell n" "T' = T"
      and n: "n < length el"
      by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def sc_array_length_def)
    from hconf arrobj Arr have "P,h \<turnstile>sc Arr T' el \<surd>" by(auto dest: sc_hconfD)
    with n have "P,h \<turnstile>sc el ! n :\<le> T" by(fastsimp simp add: sc_oconf_def)
    thus ?thesis using Arr arrobj n by(auto intro: sc_heap_read.intros)
  qed
next
  fix h a al T v
  assume alt: "sc.addr_loc_type P h a al T"
  from alt obtain arrobj where arrobj: "h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
  thus "\<exists>h'. sc_heap_write h a al v h'" using alt
    by(cases arrobj)(auto intro: sc_heap_write.intros elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
qed

interpretation sc!: heap_progress
  "empty"
  "sc_new_obj P"
  "sc_new_arr" 
  "sc_typeof_addr"
  "sc_array_length"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P
by(rule sc_heap_progress)

lemma sc_heap_conf_read:
  "heap_conf_read empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_read sc_heap_write (sc_hconf P) P"
proof
  fix h a al v T
  assume read: "sc_heap_read h a al v"
    and alt: "sc.addr_loc_type P h a al T"
    and hconf: "P \<turnstile>sc h \<surd>"
  thus "P,h \<turnstile>sc v :\<le> T"
    by(auto elim!: sc_heap_read.cases sc.addr_loc_type.cases simp add: sc_typeof_addr_def)(fastsimp dest!: sc_hconfD simp add: sc_oconf_def)+
qed

interpretation sc!: heap_conf_read
  "empty"
  "sc_new_obj P"
  "sc_new_arr" 
  "sc_typeof_addr"
  "sc_array_length"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P
by(rule sc_heap_conf_read)

end
