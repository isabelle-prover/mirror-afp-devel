theory SC_Collections imports
  "../Common/Conform"
  "../../Collections/RBTMapImpl"
  "../../Collections/TrieMapImpl"
  "../../Collections/ListMapImpl"
begin

subsection{* Objects and Arrays *}

types 
  fields = "(char, (cname, val) lm) tm"       -- "field name, defining class, value"
  array_cells = "(nat, val) rbt"

datatype heapobj
  = Obj cname fields                    -- "class instance with class name and fields"
  | Arr ty nat array_cells                 -- "element type, size and cell contents"

lemma heapobj_rec [simp]: "heapobj_rec = heapobj_case"
by(auto intro!: ext split: heapobj.split)

primrec obj_ty  :: "heapobj \<Rightarrow> ty"
where
  "obj_ty (Obj c f)   = Class c"
| "obj_ty (Arr t si e) = Array t"

fun is_Arr :: "heapobj \<Rightarrow> bool" where
  "is_Arr (Obj C fs)    = False"
| "is_Arr (Arr T si el) = True"

lemma is_Arr_conv:
  "is_Arr arrobj = (\<exists>T si el. arrobj = Arr T si el)"
by(cases arrobj, auto)

lemma is_ArrE:
  "\<lbrakk> is_Arr arrobj; \<And>T si el. arrobj = Arr T si el \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
  "\<lbrakk> \<not> is_Arr arrobj; \<And>C fs. arrobj = Obj C fs \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(cases arrobj, auto)+

definition init_fields :: "((vname \<times> cname) \<times> ty) list \<Rightarrow> fields"
where
  "init_fields FDTs \<equiv>
  foldr (\<lambda>((F, D), T) fields. 
           let F' = explode F
           in tm_update F' (lm_update D (default_val T)
                                      (case tm_lookup F' fields of None \<Rightarrow> lm_empty | Some lm \<Rightarrow> lm)) fields)
        FDTs tm_empty"

definition
  -- "a new, blank object with default values in all fields:"
  blank :: "'m prog \<Rightarrow> cname \<Rightarrow> heapobj"
where
  "blank P C  \<equiv>  Obj C (init_fields (map (\<lambda>(FD, (T, fm)). (FD, T)) (TypeRel.fields P C)))"

lemma blank_obj: "\<exists>c f. blank P C = Obj c f"
by(simp add: blank_def)

lemma obj_ty_blank [iff]: "obj_ty (blank P C) = Class C"
  by (simp add: blank_def)

subsection{* Heap *}

types heap = "(addr, heapobj) rbt"

translations
  (type) "heap" <= (type) "(nat, heapobj) rbt"

abbreviation sc_empty :: heap
where "sc_empty \<equiv> rm_empty"

fun the_obj :: "heapobj \<Rightarrow> cname \<times> fields" where
  "the_obj (Obj C fs) = (C, fs)"

fun the_arr :: "heapobj \<Rightarrow> ty \<times> nat \<times> array_cells" where
  "the_arr (Arr T si el) = (T, si, el)"

abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the_obj (the (rm_lookup a hp)))"

definition new_Addr :: "heap \<Rightarrow> addr option"
where "new_Addr h = Some (case rm_max h (\<lambda>_ _. True) of None \<Rightarrow> 0 | Some (a, _) \<Rightarrow> a + 1)"

definition sc_new_obj :: "'m prog \<Rightarrow> heap \<Rightarrow> cname \<Rightarrow> (heap \<times> addr option)"
where
  "sc_new_obj P h C = 
   (case new_Addr h of None \<Rightarrow> (h, None)
                   | Some a \<Rightarrow> (rm_update a (blank P C) h, Some a))"

definition sc_new_arr :: "heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> (heap \<times> addr option)"
where
  "sc_new_arr h T n =
  (case new_Addr h of None \<Rightarrow> (h, None)
                  | Some a \<Rightarrow> (rm_update a (Arr T n (foldl (\<lambda>cells i. rm_update i (default_val T) cells) rm_empty [0..<n])) h, Some a))"

definition sc_typeof_addr :: "heap \<Rightarrow> addr \<Rightarrow> ty option"
where "sc_typeof_addr h a = Option.map obj_ty (rm_lookup a h)"

definition sc_array_length :: "heap \<Rightarrow> addr \<Rightarrow> nat"
where "sc_array_length h a = (case the (rm_lookup a h) of Arr T si el \<Rightarrow> si | _ \<Rightarrow> undefined)"

inductive sc_heap_read :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
for h :: heap and a :: addr
where
  Obj: "\<lbrakk> rm_lookup a h = \<lfloor>Obj C fs\<rfloor>; tm_lookup (explode F) fs = \<lfloor>fs'\<rfloor>; lm_lookup D fs' = \<lfloor>v\<rfloor> \<rbrakk> \<Longrightarrow> sc_heap_read h a (CField D F) v"
| Arr: "\<lbrakk> rm_lookup a h = \<lfloor>Arr T si el\<rfloor>; n < si \<rbrakk> \<Longrightarrow> sc_heap_read h a (ACell n) (the (rm_lookup n el))"

hide_fact (open) Obj Arr

inductive_cases sc_heap_read_cases [elim!]:
  "sc_heap_read h a (CField C F) v"
  "sc_heap_read h a (ACell n) v"

inductive sc_heap_write :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> heap \<Rightarrow> bool"
for h :: heap and a :: addr
where
  Obj:
  "\<lbrakk> rm_lookup a h = \<lfloor>Obj C fs\<rfloor>; F' = explode F;
     h' = rm_update a (Obj C (tm_update F' (lm_update D v (case tm_lookup (explode F) fs of None \<Rightarrow> lm_empty | Some fs' \<Rightarrow> fs')) fs)) h \<rbrakk>
  \<Longrightarrow> sc_heap_write h a (CField D F) v h'"

| Arr:
  "\<lbrakk> rm_lookup a h = \<lfloor>Arr T si el\<rfloor>; h' = rm_update a (Arr T si (rm_update n v el)) h \<rbrakk>
  \<Longrightarrow> sc_heap_write h a (ACell n) v h'"

hide_fact (open) Obj Arr

inductive_cases sc_heap_write_cases [elim!]:
  "sc_heap_write h a (CField C F) v h'"
  "sc_heap_write h a (ACell n) v h'"

lemma new_Addr_SomeD: "new_Addr h = \<lfloor>a\<rfloor> \<Longrightarrow> rm_lookup a h = None"
apply(simp add: new_Addr_def)
apply(drule rm.max_None[OF TrueI])
apply(simp add: rm.lookup_correct rel_of_def)
apply(clarsimp simp add: rm.lookup_correct)
apply(frule rm.max_Some[OF TrueI])
apply(clarsimp simp add: rel_of_def)
apply(rule ccontr)
apply(clarsimp)
apply(drule_tac k'="Suc a" in rm.max_Some(2)[OF TrueI])
apply(auto simp add: rel_of_def)
done

interpretation sc!: 
  heap_base
    "sc_empty"
    "sc_new_obj P"
    "sc_new_arr" 
    "sc_typeof_addr"
    "sc_array_length"
    "sc_heap_read"
    "sc_heap_write"
  for P .

text {* Translate notation from @{text heap_base} *}

abbreviation sc_preallocated :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"
where "sc_preallocated == sc.preallocated TYPE('m)"

abbreviation sc_start_tid :: "'md prog \<Rightarrow> thread_id"
where "sc_start_tid \<equiv> sc.start_tid TYPE('md)"

notation sc.conf ("_,_ \<turnstile>sc _ :\<le> _"  [51,51,51,51] 50)
notation sc.hext ("_ \<unlhd>sc _" [51,51] 50)

lemma sc_heap: "heap sc_empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_write"
proof
  show "sc_typeof_addr sc_empty = empty"
    by(auto simp add: sc_typeof_addr_def rm.lookup_correct rm.empty_correct intro!: ext)
next
  fix h C h' a
  assume "sc_new_obj P h C = (h', \<lfloor>a\<rfloor>)"
  thus "sc_typeof_addr h a = None \<and> sc_typeof_addr h' a = \<lfloor>Class C\<rfloor>"
    by(auto simp add: sc_new_obj_def sc_typeof_addr_def rm.lookup_correct rm.update_correct dest: new_Addr_SomeD split: split_if_asm)
next
  fix h C h' a
  assume "sc_new_obj P h C = (h', a)"
  thus "h \<unlhd>sc h'"
    by(force simp add: sc_new_obj_def sc_typeof_addr_def sc_array_length_def rm.lookup_correct rm.update_correct intro!: sc.hextI dest: new_Addr_SomeD[OF sym] split: heapobj.split split_if_asm)
next
  fix h T n h' a
  assume "sc_new_arr h T n = (h', \<lfloor>a\<rfloor>)"
  thus "sc_typeof_addr h a = None \<and> sc_typeof_addr h' a = \<lfloor>T\<lfloor>\<rceil>\<rfloor> \<and> sc_array_length h' a = n"
    by(auto simp add: sc_new_arr_def sc_typeof_addr_def sc_array_length_def rm.lookup_correct rm.update_correct dest: new_Addr_SomeD split: split_if_asm)
next
  fix h T n h' a
  assume "sc_new_arr h T n = (h', a)"
  thus "h \<unlhd>sc h'"
    by(force intro!: sc.hextI simp add: sc_typeof_addr_def sc_new_arr_def sc_array_length_def rm.lookup_correct rm.update_correct dest: new_Addr_SomeD[OF sym] split: split_if_asm)
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
    by(cases al)(auto intro!: sc.hextI simp add: sc_typeof_addr_def sc_array_length_def rm.lookup_correct rm.update_correct)
qed

interpretation sc!: 
  heap 
    "sc_empty"
    "sc_new_obj P"
    "sc_new_arr" 
    "sc_typeof_addr"
    "sc_array_length"
    "sc_heap_read"
    "sc_heap_write"
  for P by(rule sc_heap)

lemma sc_hext_new:
  "rm_lookup a h = None \<Longrightarrow> h \<unlhd>sc rm_update a arrobj h"
by(rule sc.hextI)(auto simp add: sc_typeof_addr_def sc_array_length_def rm.lookup_correct rm.update_correct dest!: new_Addr_SomeD)

lemma sc_hext_upd_obj: "rm_lookup a h = Some (Obj C fs) \<Longrightarrow> h \<unlhd>sc rm_update a (Obj C fs') h"
by(rule sc.hextI)(auto simp:fun_upd_apply sc_typeof_addr_def sc_array_length_def rm.lookup_correct rm.update_correct)

lemma sc_hext_upd_arr: "\<lbrakk> rm_lookup a h = Some (Arr T si e) \<rbrakk> \<Longrightarrow> h \<unlhd>sc rm_update a (Arr T si e') h"
by(rule sc.hextI)(auto simp:fun_upd_apply sc_typeof_addr_def sc_array_length_def rm.lookup_correct rm.update_correct)

subsection {* Conformance *}

definition sc_oconf :: "'m prog \<Rightarrow> heap \<Rightarrow> heapobj \<Rightarrow> bool"   ("_,_ \<turnstile>sc _ \<surd>" [51,51,51] 50)
where
  "P,h \<turnstile>sc obj \<surd>  \<equiv>
   (case obj of Obj C fs \<Rightarrow> is_class P C \<and> (\<forall>F D T fm. P \<turnstile> C has F:T (fm) in D \<longrightarrow> (\<exists>fs' v. tm_\<alpha> fs (explode F) = Some fs' \<and> lm_\<alpha> fs' D = Some v \<and> P,h \<turnstile>sc v :\<le> T))
              | Arr T si el \<Rightarrow> is_type P T \<and> (\<forall>n. n < si \<longrightarrow> (\<exists>v. rm_\<alpha> el n = Some v \<and> P,h \<turnstile>sc v :\<le> T)))"

definition sc_hconf :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"  ("_ \<turnstile>sc _ \<surd>" [51,51] 50)
where "P \<turnstile>sc h \<surd> \<longleftrightarrow> (\<forall>a obj. rm_\<alpha> h a = Some obj \<longrightarrow> P,h \<turnstile>sc obj \<surd>)"

interpretation sc!: heap_conf_base  
  "sc_empty"
  "sc_new_obj P"
  "sc_new_arr" 
  "sc_typeof_addr"
  "sc_array_length"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P .

lemma sc_conf_upd_obj: "rm_lookup a h = Some(Obj C fs) \<Longrightarrow> (P,rm_update a (Obj C fs') h \<turnstile>sc x :\<le> T) = (P,h \<turnstile>sc x :\<le> T)"
apply (unfold sc.conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
apply (auto simp add: sc_typeof_addr_def rm.lookup_correct rm.update_correct split: split_if_asm)
done

lemma sc_conf_upd_arr: "rm_lookup a h = Some(Arr T si el) \<Longrightarrow> (P,rm_update a (Arr T si el') h \<turnstile>sc x :\<le> T') = (P,h \<turnstile>sc x :\<le> T')"
apply(unfold sc.conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
apply(auto simp add: sc_typeof_addr_def rm.lookup_correct rm.update_correct split: split_if_asm)
done

lemma sc_oconf_hext: "P,h \<turnstile>sc obj \<surd> \<Longrightarrow> h \<unlhd>sc h' \<Longrightarrow> P,h' \<turnstile>sc obj \<surd>"
unfolding sc_oconf_def
by(fastsimp split: heapobj.split elim: sc.conf_hext)

lemma map_of_fields_init_fields:
  assumes "map_of FDTs (F, D) = \<lfloor>(T, fm)\<rfloor>"
  shows "\<exists>fs' v. tm_\<alpha> (init_fields (map (\<lambda>(FD, (T, fm)). (FD, T)) FDTs)) (explode F) = \<lfloor>fs'\<rfloor> \<and> lm_\<alpha> fs' D = \<lfloor>v\<rfloor> \<and> sc.conf P h v T"
using assms
by(induct FDTs)(auto simp add: tm.lookup_correct tm.update_correct lm.update_correct init_fields_def explode_inject)

lemma sc_oconf_init_fields:
  assumes "P \<turnstile> C has_fields FDTs"
  shows "P,h \<turnstile>sc (Obj C (init_fields (map (\<lambda>(FD, (T, fm)). (FD, T)) FDTs))) \<surd>"
using assms has_fields_is_class[OF assms] map_of_fields_init_fields[of FDTs]
by(fastsimp simp add: has_field_def sc_oconf_def dest: has_fields_fun)

lemma sc_oconf_init_arr:
  assumes type: "is_type P U"
  shows "P,h \<turnstile>sc (Arr U n (foldl (\<lambda>cells i. rm_update i (default_val U) cells) rm_empty [0..<n])) \<surd>"
proof -
  { fix n'
    assume "n' < n"
    { fix rm and k :: nat
      assume "\<forall>i<k. \<exists>v. rm_\<alpha> rm i = \<lfloor>v\<rfloor> \<and> sc.conf P h v U"
      with `n' < n` have "\<exists>v. rm_\<alpha> (foldl (\<lambda>cells i. rm_update i (default_val U) cells) rm [k..<n]) n' = \<lfloor>v\<rfloor> \<and> sc.conf P h v U"
        by(induct m\<equiv>"n-k" arbitrary: n k rm)(auto simp add: rm.update_correct upt_conv_Cons type)
    }
    from this[of 0 rm_empty]
    have "\<exists>v. rm_\<alpha> (foldl (\<lambda>cells i. rm_update i (default_val U) cells) rm_empty [0..<n]) n' = \<lfloor>v\<rfloor> \<and> sc.conf P h v U" by simp
  }
  thus ?thesis using type by(simp add: sc_oconf_def)
qed

lemma sc_oconf_fupd [intro?]:
  "\<lbrakk> P \<turnstile> C has F:T (fm) in D; P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Obj C fs) \<surd>;
    fs' = (case tm_lookup (explode F) fs of None \<Rightarrow> lm_empty | Some fs' \<Rightarrow> fs') \<rbrakk>
  \<Longrightarrow> P,h \<turnstile>sc (Obj C (tm_update (explode F) (lm_update D v fs') fs)) \<surd>"
unfolding sc_oconf_def has_field_def
apply(auto dest: has_fields_fun simp add: lm.update_correct tm.update_correct tm.lookup_correct explode_inject)
apply(drule (1) has_fields_fun, fastsimp)
apply(drule (1) has_fields_fun, fastsimp)
done

lemma sc_oconf_fupd_arr [intro?]:
  "\<lbrakk> P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Arr T si el) \<surd> \<rbrakk>
  \<Longrightarrow> P,h \<turnstile>sc (Arr T si (rm_update i v el)) \<surd>"
unfolding sc_oconf_def
by(auto simp add: rm.update_correct)

lemma sc_oconf_new: "\<lbrakk> P,h \<turnstile>sc obj \<surd>; rm_lookup a h = None \<rbrakk> \<Longrightarrow> P,rm_update a arrobj h \<turnstile>sc obj \<surd>"
by(erule sc_oconf_hext)(rule sc_hext_new)

lemma sc_oconf_blank: "is_class P C \<Longrightarrow> P,h \<turnstile>sc blank P C \<surd>"
by(auto dest: map_of_fields_init_fields simp add: blank_def has_field_def sc_oconf_def)

lemmas sc_oconf_upd_obj = sc_oconf_hext [OF _ sc_hext_upd_obj]

lemma sc_oconf_upd_arr:
  "\<lbrakk> P,h \<turnstile>sc obj \<surd>; rm_lookup a h = \<lfloor>Arr T si el\<rfloor> \<rbrakk> \<Longrightarrow> P,rm_update a (Arr T si el') h \<turnstile>sc obj \<surd>"
by(fastsimp simp add: sc_oconf_def sc_conf_upd_arr split: heapobj.split)

lemma sc_hconfD: "\<lbrakk> P \<turnstile>sc h \<surd>; rm_lookup a h = Some obj \<rbrakk> \<Longrightarrow> P,h \<turnstile>sc obj \<surd>"
unfolding sc_hconf_def by(auto simp add: rm.lookup_correct)

lemmas sc_preallocated_new = sc.preallocated_hext[OF _ sc_hext_new]
lemmas sc_preallocated_upd_obj = sc.preallocated_hext [OF _ sc_hext_upd_obj]
lemmas sc_preallocated_upd_arr = sc.preallocated_hext [OF _ sc_hext_upd_arr]

lemma sc_hconf_new: "\<lbrakk> P \<turnstile>sc h \<surd>; rm_lookup a h = None; P,h \<turnstile>sc obj \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc rm_update a obj h \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_new simp add: rm.lookup_correct rm.update_correct)

lemma sc_hconf_upd_obj: "\<lbrakk> P \<turnstile>sc h \<surd>; rm_lookup a h = Some (Obj C fs); P,h \<turnstile>sc (Obj C fs') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc rm_update a (Obj C fs') h \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_upd_obj simp add: rm.lookup_correct rm.update_correct)

lemma sc_hconf_upd_arr: "\<lbrakk> P \<turnstile>sc h \<surd>; rm_lookup a h = Some(Arr T si el); P,h \<turnstile>sc (Arr T si el') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc rm_update a (Arr T si el') h \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_upd_arr simp add: rm.lookup_correct rm.update_correct)

lemma sc_heap_conf: 
  "heap_conf sc_empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_write (sc_hconf P) P"
proof
  show "P \<turnstile>sc sc_empty \<surd>" by(simp add: sc_hconf_def rm.empty_correct)
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
  "sc_empty"
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
  "heap_progress sc_empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_read sc_heap_write (sc_hconf P) P"
proof
  fix h a al T
  assume hconf: "P \<turnstile>sc h \<surd>"
    and alt: "sc.addr_loc_type P h a al T"
  from alt obtain arrobj where arrobj: "rm_lookup a h = \<lfloor>arrobj\<rfloor>"
    by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
  show "\<exists>v. sc_heap_read h a al v \<and> P,h \<turnstile>sc v :\<le> T"
  proof(cases arrobj)
    case (Obj C fs)
    with alt arrobj obtain D F fm
      where [simp]: "al = CField D F"
      and "P \<turnstile> C has F:T (fm) in D"
      by(fastsimp elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
    from hconf arrobj Obj have "P,h \<turnstile>sc Obj C fs \<surd>" by(auto dest: sc_hconfD)
    with `P \<turnstile> C has F:T (fm) in D` obtain fs' v 
      where "tm_lookup (explode F) fs = \<lfloor>fs'\<rfloor>" "lm_lookup D fs' = \<lfloor>v\<rfloor>" "P,h \<turnstile>sc v :\<le> T"
      by(fastsimp simp add: sc_oconf_def tm.lookup_correct lm.lookup_correct)
    thus ?thesis using Obj arrobj by(auto intro: sc_heap_read.intros)
  next
    case (Arr T' si el)
    with alt arrobj obtain n 
      where [simp]: "al = ACell n" "T' = T"
      and n: "n < si"
      by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def sc_array_length_def)
    from hconf arrobj Arr have "P,h \<turnstile>sc Arr T' si el \<surd>" by(auto dest: sc_hconfD)
    with n obtain v where "rm_lookup n el = \<lfloor>v\<rfloor>" "P,h \<turnstile>sc v :\<le> T"
      by(auto simp add: sc_oconf_def rm.lookup_correct)
    thus ?thesis using Arr arrobj n by(auto intro: sc_heap_read.intros)
  qed
next
  fix h a al T v
  assume alt: "sc.addr_loc_type P h a al T"
  from alt obtain arrobj where arrobj: "rm_lookup a h = \<lfloor>arrobj\<rfloor>"
    by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
  thus "\<exists>h'. sc_heap_write h a al v h'" using alt
    by(cases arrobj)(auto intro: sc_heap_write.intros elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
qed

interpretation sc!: heap_progress
  "sc_empty"
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
  "heap_conf_read sc_empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_read sc_heap_write (sc_hconf P) P"
proof
  fix h a al v T
  assume read: "sc_heap_read h a al v"
    and alt: "sc.addr_loc_type P h a al T"
    and hconf: "P \<turnstile>sc h \<surd>"
  thus "P,h \<turnstile>sc v :\<le> T"
    apply(auto elim!: sc_heap_read.cases sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
    apply(fastsimp dest!: sc_hconfD simp add: sc_oconf_def tm.lookup_correct lm.lookup_correct rm.lookup_correct)+
    done
qed

interpretation sc!: heap_conf_read
  "sc_empty"
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

lemma sc_deterministic_heap_ops: sc.deterministic_heap_ops
by(rule sc.deterministic_heap_opsI)(auto elim: sc_heap_read.cases sc_heap_write.cases)

subsection {* Code generation *}

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  sc_heap_read .

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  sc_heap_write .

end