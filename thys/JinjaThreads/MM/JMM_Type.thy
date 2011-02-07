(*  Title:      JinjaThreads/MM/JMM_Type.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Heap implementation for the JMM} *}

theory JMM_Type imports 
  MM
  "../Common/ExternalCallWF"
  "../Common/ConformThreaded"
begin

section {* Definitions *}

text {*
  The JMM heap only stores type information.
*}

types JMM_heap = "addr \<rightharpoonup> htype"

primrec alen_of_htype :: "htype \<Rightarrow> nat"
where
  "alen_of_htype (Array_type T n) = n"

abbreviation jmm_empty :: "JMM_heap" where "jmm_empty == Map.empty"

definition jmm_new_obj :: "JMM_heap \<Rightarrow> cname \<Rightarrow> JMM_heap \<times> addr option"
where "jmm_new_obj h C = (case new_Addr h of None \<Rightarrow> (h, None) | Some a \<Rightarrow> (h(a \<mapsto> Class_type C), Some a))"

definition jmm_new_arr :: "JMM_heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> JMM_heap \<times> addr option"
where "jmm_new_arr h T n = (case new_Addr h of None \<Rightarrow> (h, None) | Some a \<Rightarrow> (h(a \<mapsto> Array_type T n), Some a))"

definition jmm_typeof_addr :: "JMM_heap \<Rightarrow> addr \<rightharpoonup> ty"
where "jmm_typeof_addr h a = Option.map ty_of_htype (h a)"

definition jmm_array_length :: "JMM_heap \<Rightarrow> addr \<Rightarrow> nat"
where "jmm_array_length h a = alen_of_htype (the (h a))"

definition jmm_heap_read :: "JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
where "jmm_heap_read h a ad v = True"

inductive jmm_heap_write :: "JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm_heap_write h a ad v h"

definition jmm_hconf :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> bool" ("_ \<turnstile>jmm _ \<surd>" [51,51] 50)
where "P \<turnstile>jmm h \<surd> \<longleftrightarrow> ty_of_htype ` ran h \<subseteq> {T. is_type P T}"

lemmas jmm_heap_ops_defs =
  jmm_new_obj_def jmm_new_arr_def jmm_typeof_addr_def 
  jmm_array_length_def jmm_heap_read_def jmm_heap_write_def

interpretation jmm!: heap_base
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  jmm_heap_read
  jmm_heap_write 
.

notation jmm.hext  ("_ \<unlhd>jmm _" [51,51] 50)
notation jmm.conf ("_,_ \<turnstile>jmm _ :\<le> _"  [51,51,51,51] 50)
notation jmm.addr_loc_type ("_,_ \<turnstile>jmm _@_ : _" [50, 50, 50, 50, 50] 51)
notation jmm.confs ("_,_ \<turnstile>jmm _ [:\<le>] _"  [51,51,51,51] 50)
notation jmm.tconf ("_,_ \<turnstile>jmm _ \<surd>t" [51,51,51] 50)


text {* Now a variation of the JMM with a different read operation that permits to read only type-conformant values *}

definition jmm_heap_read' :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
where "jmm_heap_read' P h a ad v \<longleftrightarrow> (\<forall>T. jmm.addr_loc_type P h a ad T \<longrightarrow> P,h \<turnstile>jmm v :\<le> T)"

definition jmm_heap_write' :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm_heap_write' P h a ad v h' \<longleftrightarrow> h = h' \<and> (\<forall>T. jmm.addr_loc_type P h a ad T \<longrightarrow> P,h \<turnstile>jmm v :\<le> T)"

interpretation jmm'!: heap_base
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  "jmm_heap_read' P"
  "jmm_heap_write' P"
  for P .

notation jmm'.hext ("_ \<unlhd>jmm' _" [51,51] 50)
notation jmm'.conf ("_,_ \<turnstile>jmm' _ :\<le> _"  [51,51,51,51] 50)
notation jmm'.addr_loc_type ("_,_ \<turnstile>jmm' _@_ : _" [50, 50, 50, 50, 50] 51)
notation jmm'.confs ("_,_ \<turnstile>jmm' _ [:\<le>] _"  [51,51,51,51] 50)
notation jmm'.tconf ("_,_ \<turnstile>jmm' _ \<surd>t" [51,51,51] 50)

section {* Heap locale interpretations *}

subsection {* Locale @{text heap} *}

lemma range_ty_of_htype: "range ty_of_htype \<subseteq> range Class \<union> range Array"
apply(rule subsetI)
apply(erule rangeE)
apply(rename_tac ht)
apply(case_tac ht)
apply auto
done

lemma jmm_heap: "heap jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_write"
proof
  show "jmm_typeof_addr jmm_empty = Map.empty"
    by(simp add: fun_eq_iff jmm_typeof_addr_def)
next
  fix h C h' a
  assume "jmm_new_obj h C = (h', \<lfloor>a\<rfloor>)"
  thus "jmm_typeof_addr h a = None \<and> jmm_typeof_addr h' a = \<lfloor>Class C\<rfloor>"
    by(auto simp add: jmm_heap_ops_defs dest: new_Addr_SomeD)
next
  fix h C h' a
  assume "jmm_new_obj h C = (h', a)"
  thus "h \<unlhd>jmm h'"
    by(fastsimp simp add: jmm_heap_ops_defs intro: jmm.hextI dest: new_Addr_SomeD[OF sym])
next
  fix h T n h' a
  assume "jmm_new_arr h T n = (h', \<lfloor>a\<rfloor>)"
  thus "jmm_typeof_addr h a = None \<and> jmm_typeof_addr h' a = \<lfloor>T\<lfloor>\<rceil>\<rfloor> \<and> jmm_array_length h' a = n"
    by(auto simp add: jmm_heap_ops_defs dest: new_Addr_SomeD)
next
  fix h T n h' a
  assume "jmm_new_arr h T n = (h', a)"
  thus "h \<unlhd>jmm h'"
    by(fastsimp simp add: jmm_heap_ops_defs intro: jmm.hextI dest: new_Addr_SomeD[OF sym])
next
  fix h
  show "ran (jmm_typeof_addr h) \<subseteq> range Class \<union> range Array" using range_ty_of_htype
    by(auto simp add: jmm_heap_ops_defs ran_def)
next
  fix h a al v h'
  assume "jmm_heap_write h a al v h'"
  thus "h \<unlhd>jmm h'" by cases auto
qed

interpretation jmm!: 
  heap
    jmm_empty
    jmm_new_obj
    jmm_new_arr
    jmm_typeof_addr
    jmm_array_length
    jmm_heap_read
    jmm_heap_write
by(rule jmm_heap)

lemma jmm'_heap: "heap jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length (jmm_heap_write' P)"
proof(unfold_locales)
  fix h a al v h'
  assume "jmm_heap_write' P h a al v h'"
  thus "h \<unlhd>jmm' h'" by(auto simp add: jmm_heap_write'_def)
qed(auto simp add: jmm.empty_heap_empty jmm.new_obj_SomeD jmm.new_arr_SomeD jmm.hext_new_obj jmm.hext_new_arr jmm.ran_typeof_addr)

interpretation jmm'!: heap
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  "jmm_heap_read' P"
  "jmm_heap_write' P"
  for P
by(rule jmm'_heap)

subsection {* Locale @{text "heap_conf"} *}

interpretation jmm!: heap_conf_base
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  jmm_heap_read
  jmm_heap_write
  "jmm_hconf P"
  P
  for P .

abbreviation (input) jmm'_hconf :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> bool" ("_ \<turnstile>jmm' _ \<surd>" [51,51] 50)
where "jmm'_hconf == jmm_hconf"

interpretation jmm'!: heap_conf_base
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  "jmm_heap_read' P"
  "jmm_heap_write' P"
  "jmm'_hconf P"
  P
  for P .

lemma jmm_heap_conf:
  "heap_conf jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_write (jmm_hconf P) P"
proof
  show "P \<turnstile>jmm jmm_empty \<surd>"
    by(simp add: jmm_hconf_def)
next
  fix h a T
  assume "jmm_typeof_addr h a = \<lfloor>T\<rfloor>" "P \<turnstile>jmm h \<surd>"
  thus "is_type P T" by(auto simp add: jmm_hconf_def jmm_heap_ops_defs intro: ranI)
next
  fix h C h' a
  assume "jmm_new_obj h C = (h', a)" "P \<turnstile>jmm h \<surd>" "is_class P C"
  thus "P \<turnstile>jmm h' \<surd>"
    by(fastsimp simp add: jmm_hconf_def jmm_heap_ops_defs ran_def split: split_if_asm)
next
  fix h T n h' a
  assume "jmm_new_arr h T n = (h', a)" "P \<turnstile>jmm h \<surd>" "is_type P T"
  thus "P \<turnstile>jmm h' \<surd>"
    by(fastsimp simp add: jmm_hconf_def jmm_heap_ops_defs ran_def split: split_if_asm)
next
  fix h a al v h' T
  assume "jmm_heap_write h a al v h'" "P \<turnstile>jmm h \<surd>"
    and "jmm.addr_loc_type P h a al T" and "P,h \<turnstile>jmm v :\<le> T"
  thus "P \<turnstile>jmm h' \<surd>" by(cases) simp
qed

interpretation jmm!: heap_conf
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  jmm_heap_read
  jmm_heap_write
  "jmm_hconf P"
  P
  for P
by(rule jmm_heap_conf)

lemma jmm'_heap_conf:
  "heap_conf jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length (jmm_heap_write' P) (jmm'_hconf P) P"
proof(unfold_locales)
  fix h a al v h' T
  assume "jmm_heap_write' P h a al v h'" "P \<turnstile>jmm' h \<surd>"
    and "jmm'.addr_loc_type P h a al T" and "P,h \<turnstile>jmm' v :\<le> T"
  thus "P \<turnstile>jmm' h' \<surd>" by(auto simp add: jmm_heap_write'_def)
qed(simp_all only: jmm.hconf_empty jmm.typeof_addr_is_type jmm.hconf_new_obj_mono jmm.hconf_new_arr_mono)

interpretation jmm'!: heap_conf
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  "jmm_heap_read' P"
  "jmm_heap_write' P"
  "jmm'_hconf P"
  P
  for P
by(rule jmm'_heap_conf)

subsection {* Locale @{text heap_progress} *}

lemma jmm_heap_progress:
  "heap_progress jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_read jmm_heap_write (jmm_hconf P) P"
proof
  fix h a al T
  assume "P \<turnstile>jmm h \<surd>"
    and al: "jmm.addr_loc_type P h a al T"
  show "\<exists>v. jmm_heap_read h a al v \<and> P,h \<turnstile>jmm v :\<le> T"
    using jmm.defval_conf[of P h T] unfolding jmm_heap_ops_defs by blast
next
  fix h a al T v
  assume "jmm.addr_loc_type P h a al T"
  show "\<exists>h'. jmm_heap_write h a al v h'"
    by(auto intro: jmm_heap_write.intros)
qed

interpretation jmm!: heap_progress
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  jmm_heap_read
  jmm_heap_write
  "jmm_hconf P"
  P
  for P
by(rule jmm_heap_progress)

lemma jmm'_heap_progress:
  "heap_progress jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length (jmm_heap_read' P) (jmm_heap_write' P) (jmm'_hconf P) P"
proof
  fix h a al T
  assume "P \<turnstile>jmm' h \<surd>"
    and al: "jmm'.addr_loc_type P h a al T"
  thus "\<exists>v. jmm_heap_read' P h a al v \<and> P,h \<turnstile>jmm' v :\<le> T"
    unfolding jmm_heap_read'_def
    by(blast dest: jmm'.addr_loc_type_fun intro: jmm'.defval_conf)+
next
  fix h a al T v
  assume "jmm'.addr_loc_type P h a al T"
    and "P,h \<turnstile>jmm' v :\<le> T"
  thus "\<exists>h'. jmm_heap_write' P h a al v h'"
    by(auto simp add: jmm_heap_write'_def dest: jmm'.addr_loc_type_fun)
qed

interpretation jmm'!: heap_progress
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  "jmm_heap_read' P"
  "jmm_heap_write' P"
  "jmm'_hconf P"
  P
  for P
by(rule jmm'_heap_progress)

subsection {* Locale @{text heap_conf_read} *}

lemma jmm'_heap_conf_read:
  "heap_conf_read jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length (jmm_heap_read' P) (jmm_heap_write' P) (jmm'_hconf P) P"
proof
  fix h a al v T
  assume "jmm_heap_read' P h a al v"
    and "jmm'.addr_loc_type P h a al T"
    and "P \<turnstile>jmm' h \<surd>"
  thus "P,h \<turnstile>jmm' v :\<le> T" by(simp add: jmm_heap_read'_def)
qed

interpretation jmm'!: heap_conf_read
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  "jmm_heap_read' P"
  "jmm_heap_write' P"
  "jmm'_hconf P"
  P
  for P
by(rule jmm'_heap_conf_read)

interpretation jmm'!: heap_typesafe
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  "jmm_heap_read' P"
  "jmm_heap_write' P"
  "jmm'_hconf P"
  P
  for P
..

subsection {* Syntax translations *}

notation jmm'.external_WT' ("_,_ \<turnstile>jmm' (_\<bullet>_'(_')) : _" [50,0,0,0,50] 60)

abbreviation jmm'_red_external :: 
  "'m prog \<Rightarrow> thread_id \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> JMM_heap external_thread_action \<Rightarrow> 
    extCallRet \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm'_red_external P \<equiv> jmm'.red_external (TYPE('m)) P P"

abbreviation jmm'_red_external_syntax :: 
  "'m prog \<Rightarrow> thread_id \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> JMM_heap \<Rightarrow> JMM_heap external_thread_action \<Rightarrow>
    extCallRet \<Rightarrow> JMM_heap \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' (\<langle>(_\<bullet>_'(_')),/_\<rangle>) -_\<rightarrow>ext (\<langle>(_),/(_)\<rangle>)" [50, 0, 0, 0, 0, 0, 0, 0, 0] 51)
where
  "P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<equiv> jmm'_red_external P t h a M vs ta va h'"

abbreviation jmm'_red_external_aggr :: 
  "'m prog \<Rightarrow> thread_id \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> JMM_heap 
    \<Rightarrow> JMM_heap external_thread_action \<times> extCallRet \<times> JMM_heap \<Rightarrow> bool"
where "jmm'_red_external_aggr P \<equiv> jmm'.red_external_aggr TYPE('m) P P"

abbreviation jmm'_heap_copy_loc :: "'m prog \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> JMM_heap \<Rightarrow> obs_event list \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm'_heap_copy_loc \<equiv> jmm'.heap_copy_loc TYPE('m)"

abbreviation jmm'_heap_copies :: "'m prog \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> addr_loc list \<Rightarrow> JMM_heap \<Rightarrow> obs_event list \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm'_heap_copies \<equiv> jmm'.heap_copies TYPE('m)"

abbreviation jmm'_heap_clone :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> JMM_heap \<Rightarrow> (obs_event list \<times> nat) option \<Rightarrow> bool"
where "jmm'_heap_clone P \<equiv> jmm'.heap_clone TYPE('m) P P"

abbreviation jmm'_heap_ops_typeof_minimal :: "'m prog \<Rightarrow> bool"
where "jmm'_heap_ops_typeof_minimal \<equiv> jmm'.heap_ops_typeof_minimal TYPE('m)"

lemma jmm_heap_ops_typeof_minimal: "jmm.heap_ops_typeof_minimal"
by(auto simp add: jmm.heap_ops_typeof_minimal_def jmm_new_obj_def jmm_new_arr_def jmm_typeof_addr_def elim: jmm_heap_write.cases)

lemma jmm'_heap_ops_typeof_minimal: "jmm'_heap_ops_typeof_minimal P"
by(auto simp add: jmm'.heap_ops_typeof_minimal_def jmm_new_obj_def jmm_new_arr_def jmm_typeof_addr_def jmm_heap_write'_def)

end