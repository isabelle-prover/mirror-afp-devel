(*  Title:      JinjaThreads/MM/JMM_Common.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{JMM Instantiation with Jinja -- common parts} *}

theory JMM_Common
imports
  JMM_Framework
  "../Common/BinOp"
  "../Common/ExternalCallWF"
begin

context heap begin

lemma heap_copy_loc_not_New: assumes "heap_copy_loc a a' al h ob h'"
  shows "NewHeapElem a'' x \<in> set ob \<Longrightarrow> False"
using assms
by(auto elim: heap_copy_loc.cases)

lemma heap_copies_not_New:
  assumes "heap_copies a a' als h obs h'" 
  and "NewHeapElem a'' x \<in> set obs"
  shows "False"
using assms
by induct(auto dest: heap_copy_loc_not_New)

lemma heap_clone_New_same_addr_same:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "obs ! i = NewHeapElem a'' x" "i < length obs"
  and "obs ! j = NewHeapElem a'' x'" "j < length obs"
  shows "i = j"
using assms
apply cases
apply(fastforce simp add: nth_Cons' gr0_conv_Suc in_set_conv_nth split: split_if_asm dest: heap_copies_not_New)+
done

lemma red_external_New_same_addr_same:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; 
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a' x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a' x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(auto elim!: red_external.cases simp add: nth_Cons' split: split_if_asm dest: heap_clone_New_same_addr_same)

lemma red_external_aggr_New_same_addr_same:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a' x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a' x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(auto simp add: external_WT_defs.simps red_external_aggr_def nth_Cons' split: split_if_asm split_if_asm dest: heap_clone_New_same_addr_same)

lemma heap_copy_loc_read_typeable:
  assumes "heap_copy_loc a a' al h obs h'"
  and "ReadMem ad al' v \<in> set obs"
  and "P,h \<turnstile> a@al : T"
  shows "ad = a \<and> al'= al"
using assms by cases auto

lemma heap_copies_read_typeable:
  assumes "heap_copies a a' als h obs h'"
  and "ReadMem ad al' v \<in> set obs"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts"
  shows "ad = a \<and> al' \<in> set als"
using assms
proof(induct arbitrary: Ts)
  case Nil thus ?case by simp
next
  case (Cons al h ob h' als obs h'')
  from `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) (al # als) Ts`
  obtain T Ts' where Ts [simp]: "Ts = T # Ts'"
    and "P,h \<turnstile> a@al : T" 
    and "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from `ReadMem ad al' v \<in> set (ob @ obs)`
  show ?case unfolding set_append Un_iff
  proof
    assume "ReadMem ad al' v \<in> set ob"
    with `heap_copy_loc a a' al h ob h'`
    have "ad = a \<and> al'= al" using `P,h \<turnstile> a@al : T`
      by(rule heap_copy_loc_read_typeable)
    thus ?thesis by simp
  next
    assume "ReadMem ad al' v \<in> set obs"
    moreover from `heap_copy_loc a a' al h ob h'`
    have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
    from `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'`
    have "list_all2 (\<lambda>al T. P,h' \<turnstile> a@al : T) als Ts'"
      by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h'`])
    ultimately have "ad = a \<and> al' \<in> set als" by(rule Cons)
    thus ?thesis by simp
  qed
qed

lemma heap_clone_read_typeable:
  assumes clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and read: "ReadMem ad al v \<in> set obs"
  shows "ad = a \<and> (\<exists>T'. P,h \<turnstile> ad@al : T')"
using clone
proof cases
  case (ObjClone C H' FDTs obs')
  let ?als = "map (\<lambda>((F, D), Tm). CField D F) FDTs"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs"
  note `heap_copies a a' ?als H' obs' h'`
  moreover
  from `obs = NewObj a' C # obs'` read 
  have "ReadMem ad al v \<in> set obs'" by simp
  moreover
  from `new_obj h C = (H', \<lfloor>a'\<rfloor>)` have "h \<unlhd> H'" by(rule hext_new_obj)
  hence "typeof_addr H' a = \<lfloor>Class C\<rfloor>" using `typeof_addr h a = \<lfloor>Class C\<rfloor>`
    by(rule typeof_addr_hext_mono)
  hence type: "list_all2 (\<lambda>al T. P,H' \<turnstile> a@al : T) ?als ?Ts"
    using `P \<turnstile> C has_fields FDTs`
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  ultimately have "ad = a \<and> al \<in> set ?als" by(rule heap_copies_read_typeable)
  hence [simp]: "ad = a" and "al \<in> set ?als" by simp_all
  then obtain F D T where [simp]: "al = CField D F" and "((F, D), T) \<in> set FDTs" by auto
  with type `h \<unlhd> H'` `typeof_addr h a = \<lfloor>Class C\<rfloor>` show ?thesis 
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce elim!: ballE[where x="((F, D), T)"] addr_loc_type.cases dest: typeof_addr_hext_mono intro: addr_loc_type.intros)
next
  case (ArrClone T n H' FDTs obs')
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs @ replicate n T"
  note FDTs = `P \<turnstile> Object has_fields FDTs`
  note `heap_copies a a' ?als H' obs' h'`
  moreover from `obs = NewArr a' T n # obs'` read
  have "ReadMem ad al v \<in> set obs'" by simp
  moreover from `new_arr h T n = (H', \<lfloor>a'\<rfloor>)`
  have "h \<unlhd> H'" by(rule hext_new_arr)
  with `typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `n = array_length h a`
  have type': "typeof_addr H' a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>" "array_length H' a = n"
    by(auto dest: typeof_addr_hext_mono hext_arrD)
  hence type: "list_all2 (\<lambda>al T. P,H' \<turnstile> a@al : T) ?als ?Ts" using FDTs
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  ultimately have "ad = a \<and> al \<in> set ?als" by(rule heap_copies_read_typeable)
  hence [simp]: "ad = a" and "al \<in> set ?als" by simp_all
  hence "al \<in> set (map (\<lambda>((F, D), Tfm). CField D F) FDTs) \<or> al \<in> set (map ACell [0..<n])" by simp
  thus ?thesis
  proof
    assume "al \<in> set (map (\<lambda>((F, D), Tfm). CField D F) FDTs)"
    then obtain F D Tfm where [simp]: "al = CField D F" and "((F, D), Tfm) \<in> set FDTs" by auto
    with type type' `h \<unlhd> H'` `typeof_addr h a = \<lfloor>Array T\<rfloor>` show ?thesis 
      by(fastforce elim!: ballE[where x="((F, D), Tfm)"] addr_loc_type.cases intro: addr_loc_type.intros simp add: list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv)
  next
    assume "al \<in> set (map ACell [0..<n])"
    then obtain n' where [simp]: "al = ACell n'" and "n' < n" by auto
    with type type' `h \<unlhd> H'` `n = array_length h a` `typeof_addr h a = \<lfloor>Array T\<rfloor>`
    show ?thesis by(fastforce dest: list_all2_nthD[where p=n'] elim: addr_loc_type.cases intro: addr_loc_type.intros)
  qed
qed

lemma red_external_read_mem_typeable:
  assumes red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T'. P,h \<turnstile> ad@al : T'"
using red read
by cases(fastforce dest: heap_clone_read_typeable intro: addr_loc_type.intros)+

end

context heap_conf begin

lemma heap_clone_array_lengthD:
  "\<lbrakk> heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>; NewArr a'' T n \<in> set obs; hconf  h\<rbrakk>
  \<Longrightarrow> array_length h' a'' = n"
by(fastforce elim!: heap_clone.cases dest: new_arr_SomeD hext_heap_copies heap_copies_not_New[where x="Array_type T n"] hext_arrD(2) typeof_addr_is_type)

lemma red_external_NewArr_lengthD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewArr a' T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; hconf h \<rbrakk>
  \<Longrightarrow> array_length h' a' = n"
by(erule red_external.cases)(auto dest: heap_clone_array_lengthD)

lemma red_external_aggr_NewArr_lengthD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; NewArr a' T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     is_native P (the (typeof_addr h a)) M; hconf h \<rbrakk>
  \<Longrightarrow> array_length h' a' = n"
by(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: split_if_asm dest: heap_clone_array_lengthD)


lemma heap_clone_typeof_addrD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "hconf h"
  shows "NewHeapElem a'' x \<in> set obs \<Longrightarrow> a'' = a' \<and> typeof_addr h' a' = Some (ty_of_htype x)"
using assms
by(fastforce elim!: heap_clone.cases dest: new_obj_SomeD new_arr_SomeD hext_heap_copies heap_copies_not_New typeof_addr_is_type elim: hext_objD hext_arrD)

lemma red_external_New_typeof_addrD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; hconf h \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = Some (ty_of_htype x)"
by(erule red_external.cases)(auto dest: heap_clone_typeof_addrD)

lemma red_external_aggr_New_typeof_addrD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     is_native P (the (typeof_addr h a)) M; hconf h \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = Some (ty_of_htype x)"
apply(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: split_if_asm)
apply(blast dest: heap_clone_typeof_addrD)+
done

end

context heap_conf begin

lemma heap_copy_loc_ta_seq_consist_typeable:
  assumes copy: "heap_copy_loc ad ad' al h obs h'"
  and sc: "ta_seq_consist P vs (llist_of (map NormalAction obs))"
  and vs: "vs_conf P h vs"
  and hconf: "hconf h"
  and wt: "P,h \<turnstile> ad@al : T" "P,h \<turnstile> ad'@al : T"
  shows "heap_base.heap_copy_loc (heap_read_typed P) heap_write ad ad' al h obs h'" (is ?thesis1)
  and "vs_conf P h' (mrw_values P vs (map NormalAction obs))" (is ?thesis2)
proof -
  from copy obtain v where obs: "obs = [ReadMem ad al v, WriteMem ad' al v]"
    and read: "heap_read h ad al v" and "write": "heap_write h ad' al v h'" by cases
  from obs sc obtain b where "vs (ad, al) = \<lfloor>(v, b)\<rfloor>" by auto
  with vs wt have v: "P,h \<turnstile> v :\<le> T" by(blast dest: vs_confD addr_loc_type_fun)+
  with read wt have "heap_read_typed P h ad al v"
    by(auto intro: heap_read_typedI dest: addr_loc_type_fun)
  thus ?thesis1 using "write" unfolding obs by(rule heap_base.heap_copy_loc.intros)

  from "write" have hext: "h \<unlhd> h'" by(rule hext_heap_write)
  with vs have "vs_conf P h' vs" by(rule vs_conf_hext)
  moreover from hext wt v have "P,h' \<turnstile> ad'@al : T" "P,h' \<turnstile> v :\<le> T"
    by(blast intro: addr_loc_type_hext_mono conf_hext)+
  ultimately show ?thesis2 using obs by(auto intro!: vs_confI split: split_if_asm dest: vs_confD)
qed

lemma heap_copies_ta_seq_consist_typeable:
  assumes "heap_copies ad ad' als h obs h'"
  and "ta_seq_consist P vs (llist_of (map NormalAction obs))"
  and "vs_conf P h vs"
  and "hconf h"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts" "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts"
  shows "heap_base.heap_copies (heap_read_typed P) heap_write ad ad' als h obs h'" (is ?thesis1)
  and "vs_conf P h' (mrw_values P vs (map NormalAction obs))" (is ?thesis2)
using assms
proof(induct arbitrary: Ts vs)
  case Nil case 1 show ?case by(auto intro: heap_base.heap_copies.intros)
next
  case Nil case 2 thus ?case by simp
next
  case (Cons al h ob h' als obs h'')
  fix Ts vs
  assume sc: "ta_seq_consist P vs (llist_of (map NormalAction (ob @ obs)))"
    and vs: "vs_conf P h vs"
    and hconf: "hconf h"
    and wt: "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) (al # als) Ts" "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) (al # als) Ts"
  
  have sc1: "ta_seq_consist P vs (llist_of (map NormalAction ob))" 
    and sc2: "ta_seq_consist P (mrw_values P vs (map NormalAction ob)) (llist_of (map NormalAction obs))"
    using sc by(simp_all add: ta_seq_consist_lappend lappend_llist_of_llist_of[symmetric] del: lappend_llist_of_llist_of)
  from wt obtain T Ts' where Ts: "Ts = T # Ts'" 
    and wt1: "P,h \<turnstile> ad@al : T" "P,h \<turnstile> ad'@al : T"
    and wt2: "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts'" "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from `heap_copy_loc ad ad' al h ob h'` sc1 vs hconf wt1
  have copy: "heap_base.heap_copy_loc (heap_read_typed P) heap_write ad ad' al h ob h'"
    and vs': "vs_conf P h' (mrw_values P vs (map NormalAction ob))"
    by(rule heap_copy_loc_ta_seq_consist_typeable)+
  from `heap_copy_loc ad ad' al h ob h'`
  have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
  with wt2 have wt2': "list_all2 (\<lambda>al T. P,h' \<turnstile> ad@al : T) als Ts'" "list_all2 (\<lambda>al T. P,h' \<turnstile> ad'@al : T) als Ts'"
    by -(erule list_all2_mono[OF _ addr_loc_type_hext_mono], assumption+)+

  from copy hconf wt1 have hconf': "hconf h'"
    by(rule heap_conf_read.hconf_heap_copy_loc_mono[OF heap_conf_read_heap_read_typed])
  
  { case 1
    from sc2 vs' hconf' wt2' have "heap_base.heap_copies (heap_read_typed P) heap_write ad ad' als h' obs h''" by(rule Cons)
    with copy show ?case by(rule heap_base.heap_copies.Cons) }

  (* case 2 *)
  have "vs_conf P h'' (mrw_values P (mrw_values P vs (map NormalAction ob)) (map NormalAction obs))"
    using sc2 vs' hconf' wt2' by(rule Cons)
  thus "vs_conf P h'' (mrw_values P vs (map NormalAction (ob @ obs)))" by simp
qed

lemma heap_clone_ta_seq_consist_typeable_Some:
  assumes clone: "heap_clone P h ad h' \<lfloor>(obs, ad')\<rfloor>"
  and sc: "ta_seq_consist P vs (llist_of (map NormalAction obs))"
  and vs: "vs_conf P h vs"
  and hconf: "hconf h"
  shows "heap_base.heap_clone new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write P h ad h' \<lfloor>(obs, ad')\<rfloor>" (is ?thesis1)
  and "vs_conf P h' (mrw_values P vs (map NormalAction obs))" (is ?thesis2)
proof -
  have "?thesis1 \<and> ?thesis2" using clone
  proof(cases)
    case (ObjClone C h'' FDTs obs')
    note FDTs = `P \<turnstile> C has_fields FDTs`
      and obs = `obs = NewObj ad' C # obs'`
    let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs"
    let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs"
    let ?vs = "mrw_value P vs (NormalAction (NewObj ad' C :: ('addr, 'thread_id) obs_event))"
    from `new_obj h C = (h'', \<lfloor>ad'\<rfloor>)` have hext: "h \<unlhd> h''" by(rule hext_heap_ops)
    hence type: "typeof_addr h'' ad = \<lfloor>Class C\<rfloor>" using `typeof_addr h ad = \<lfloor>Class C\<rfloor>` 
      by(rule typeof_addr_hext_mono)
    
    note `heap_copies ad ad' ?als h'' obs' h'`
    moreover from sc have "ta_seq_consist P ?vs (llist_of (map NormalAction obs'))" by(simp add: obs)
    moreover from vs `new_obj h C = (h'', \<lfloor>ad'\<rfloor>)`
    have "vs_conf P h'' ?vs" by(rule vs_conf_new_obj)
    moreover from `P \<turnstile> C has_fields FDTs`
    have "is_class P C" by(rule has_fields_is_class)
    with `new_obj h C = (h'', \<lfloor>ad'\<rfloor>)` hconf have "hconf h''" by(rule hconf_new_obj_mono)
    moreover from type FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad@al : T) ?als ?Ts"
      unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
      by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
    moreover from `new_obj h C = (h'', \<lfloor>ad'\<rfloor>)` `is_class P C`
    have "typeof_addr h'' ad' = \<lfloor>(Class C)\<rfloor>" by(auto dest: new_obj_SomeD)
    with FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad'@al : T) ?als ?Ts"
      unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
      by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
    ultimately
    have copy: "heap_base.heap_copies (heap_read_typed P) heap_write ad ad' (map (\<lambda>((F, D), Tfm). CField D F) FDTs) h'' obs' h'"
      and vs': "vs_conf P h' (mrw_values P ?vs (map NormalAction obs'))"
      by(rule heap_copies_ta_seq_consist_typeable)+
    from `typeof_addr h ad = \<lfloor>Class C\<rfloor>` `new_obj h C = (h'', \<lfloor>ad'\<rfloor>)` FDTs copy
    have "?thesis1" unfolding obs by(rule heap_base.heap_clone.intros)
    moreover from vs' obs have ?thesis2 by simp
    ultimately show ?thesis ..
  next
    case (ArrClone T n h'' FDTs obs')
    note n [simp] = `n = array_length h ad`
      and obs = `obs = NewArr ad' T n # obs'`
      and new = `new_arr h T n = (h'', \<lfloor>ad'\<rfloor>)`
      and FDTs = `P \<turnstile> Object has_fields FDTs`
    let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]"
    let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs @ replicate n T"
    let ?vs = "mrw_value P vs (NormalAction (NewArr ad' T n :: ('addr, 'thread_id) obs_event))"
    from new have hext: "h \<unlhd> h''" by(rule hext_heap_ops)
    hence type: "typeof_addr h'' ad = \<lfloor>T\<lfloor>\<rceil>\<rfloor>" using `typeof_addr h ad = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` 
      by(rule typeof_addr_hext_mono)
    
    note `heap_copies ad ad' ?als h'' obs' h'`
    moreover from sc have "ta_seq_consist P ?vs (llist_of (map NormalAction obs'))" by(simp add: obs)
    moreover from `typeof_addr h ad = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `hconf h` have "is_type P (T\<lfloor>\<rceil>)"
      by(auto dest: typeof_addr_is_type)
    with vs new have "vs_conf P h'' ?vs" by(rule vs_conf_new_arr)
    moreover from new hconf `is_type P (T\<lfloor>\<rceil>)` have "hconf h''" by(rule hconf_new_arr_mono)
    moreover from hext `typeof_addr h ad = \<lfloor>T\<lfloor>\<rceil>\<rfloor>`
    have [simp]: "array_length h'' ad = array_length h ad" by(auto intro: hext_arrD)
    from type FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad@al : T) ?als ?Ts"
      by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
    moreover from new `is_type P (T\<lfloor>\<rceil>)`
    have "typeof_addr h'' ad' = \<lfloor>Array T\<rfloor>" "array_length h'' ad' = array_length h ad"
      by(auto dest: new_arr_SomeD)
    hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad'@al : T) ?als ?Ts" using FDTs
      by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
    ultimately have copy: "heap_base.heap_copies (heap_read_typed P) heap_write ad ad' (map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]) h'' obs' h'"
      and vs': "vs_conf P h' (mrw_values P ?vs (map NormalAction obs'))"
      by(rule heap_copies_ta_seq_consist_typeable)+
    from `typeof_addr h ad = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` n new FDTs copy have ?thesis1
      unfolding obs by(rule heap_base.heap_clone.ArrClone)
    moreover from vs' obs have ?thesis2 by simp
    ultimately show ?thesis ..
  qed
  thus ?thesis1 ?thesis2 by blast+
qed

lemma heap_clone_ta_seq_consist_typeable_None:
  assumes "heap_clone P h ad h' None"
  shows "heap_base.heap_clone new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write P h ad h' None"
using assms
by(cases)(blast intro: heap_base.heap_clone.intros)+

lemma red_external_ta_seq_consist_typeable:
  assumes red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and sc: "ta_seq_consist P Vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and vs: "vs_conf P h Vs"
  and hconf: "hconf h"
  shows "heap_base.red_external addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write P t h a M vs ta va h'" (is ?thesis1)
  and "vs_conf P h' (mrw_values P Vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" (is ?thesis2)
proof -
  have "?thesis1 \<and> ?thesis2" using assms
    by(cases)(auto intro: heap_base.red_external.intros heap_clone_ta_seq_consist_typeable_None heap_clone_ta_seq_consist_typeable_Some dest: hext_heap_clone elim: vs_conf_hext)
  thus ?thesis1 ?thesis2 by(blast)+
qed

lemma red_external_aggr_ta_seq_consist_typeable:
  assumes red: "(ta, va, h') \<in> red_external_aggr P t a M vs h"
  and sc: "ta_seq_consist P Vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and vs: "vs_conf P h Vs"
  and hconf: "hconf h"
  and native: "is_native P (the (typeof_addr h a)) M"
  shows "(ta, va, h') \<in> heap_base.red_external_aggr addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write P t a M vs h" (is ?thesis1)
  and "vs_conf P h' (mrw_values P Vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" (is ?thesis2)
proof -
  have "?thesis1 \<and> ?thesis2" using assms
    by(auto 4 3 simp add: is_native.simps external_WT_defs.simps red_external_aggr_def heap_base.red_external_aggr_def split: split_if_asm split del: split_if del: disjCI intro: heap_clone_ta_seq_consist_typeable_None heap_clone_ta_seq_consist_typeable_Some dest: hext_heap_clone elim: vs_conf_hext is_class_type_of.cases dest: sees_method_decl_above)
  thus ?thesis1 ?thesis2 by(blast)+
qed

end

declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

context heap_progress begin

lemma heap_copy_loc_cut_and_update:
  assumes hrt: "heap_read_typeable"
  and vs: "vs_conf P h vs"
  and dom_vs: "(a, al) \<in> dom vs"
  and type: "P,h \<turnstile> a@al : T" "P,h \<turnstile> a'@al : T"
  and hconf: "hconf h"
  shows "\<exists>obs'' h''. heap_copy_loc a a' al h obs'' h'' \<and>
                     ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction [ReadMem a al v, WriteMem a' al v]) (map NormalAction obs'') vs"
proof -
  from dom_vs obtain v' b where v'b: "vs (a, al) = \<lfloor>(v', b)\<rfloor>" by auto
  with vs type have conf: "P,h \<turnstile> v' :\<le> T" by(auto dest: addr_loc_type_fun vs_confD)
  let ?obs'' = "[ReadMem a al v', WriteMem a' al v']"
  from hrt type(1) conf hconf have "heap_read h a al v'" by(rule heap_read_typeableD)
  moreover from heap_write_total[OF hconf type(2) conf] 
  obtain h'' where "heap_write h a' al v' h''" ..
  ultimately have "heap_copy_loc a a' al h ?obs'' h''" ..
  moreover have "ta_seq_consist P vs (llist_of (map NormalAction ?obs''))"
    using v'b by simp
  moreover have "eq_upto_seq_inconsist P (map NormalAction [ReadMem a al v, WriteMem a' al v]) (map NormalAction ?obs'') vs"
    using v'b by(simp)
  ultimately show ?thesis by blast
qed

lemma heap_copies_cut_and_update:
  assumes hrt: "heap_read_typeable"
  and copies: "heap_copies a a' als h obs h'"
  and vs: "vs_conf P h vs"
  and dom_vs: "Pair a ` set als \<subseteq> dom vs"
  and type1: "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts"
  and type2: "list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts"
  and hconf: "hconf h"
  shows "\<exists>obs'' h''. heap_copies a a' als h obs'' h'' \<and>
                     ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction obs'') vs"
    (is "?concl als h obs vs")
using copies vs dom_vs type1 type2 hconf
proof(induct arbitrary: h Ts vs)
  case Nil thus ?case by(auto intro: heap_copies.Nil)
next
  case (Cons al H ob h' als obs h'' h Ts vs)
  note vs = `vs_conf P h vs`
  have dom_vs: "Pair a ` set (al # als) \<subseteq> dom vs" by fact
  note type1 = `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) (al # als) Ts`
    and type2 = `list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) (al # als) Ts`
  note hconf = `hconf h`

  from type1 obtain T Ts' where Ts: "Ts = T # Ts'"
    and type1': "P,h \<turnstile> a@al : T"
    and type1'': "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from type2 Ts have type2': "P,h \<turnstile> a'@al : T"
    and type2'': "list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts'"
    by simp_all
  from `heap_copy_loc a a' al H ob h'`
  obtain v where ob: "ob = [ReadMem a al v, WriteMem a' al v]" by cases
  from dom_vs have dom_vs1: "(a, al) \<in> dom vs" and dom_vs2: "Pair a ` set als \<subseteq> dom vs" by simp_all
  with heap_copy_loc_cut_and_update[OF hrt vs dom_vs1 type1' type2' hconf, where v=v] ob
  obtain OB H' where hcl: "heap_copy_loc a a' al h OB H'"
    and sc: "ta_seq_consist P vs (llist_of (map NormalAction OB))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction ob) (map NormalAction OB) vs" by auto
  from hcl have hext: "h \<unlhd> H'" by(rule hext_heap_copy_loc)

  let ?vs' = "mrw_values P vs (map NormalAction OB)"
  
  from hcl sc vs hconf type1' type2' have "vs_conf P H' ?vs'"
    by(rule heap_copy_loc_ta_seq_consist_typeable)
  moreover
  from dom_vs2 mrw_values_dom_mono
  have "Pair a ` set als \<subseteq> dom ?vs'" by blast
  moreover from type1'' have "list_all2 (\<lambda>al T. P,H' \<turnstile> a@al : T) als Ts'"
    by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ hext])
  moreover from type2'' have "list_all2 (\<lambda>al T. P,H' \<turnstile> a'@al : T) als Ts'"
    by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ hext])
  moreover have "hconf H'" 
    by(rule heap_conf_read.hconf_heap_copy_loc_mono[OF heap_conf_read_heap_read_typed])(rule heap_copy_loc_ta_seq_consist_typeable[OF hcl sc vs hconf type1' type2'], fact+)
  ultimately have "?concl als H' obs ?vs'" by(rule Cons.hyps)
  then obtain OBS H''
    where copies: "heap_copies a a' als H' OBS H''"
    and sc': "ta_seq_consist P ?vs' (llist_of (map NormalAction OBS))"
    and eq': "eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction OBS) ?vs'" by blast
  from hcl copies have "heap_copies a a' (al#als) h (OB @ OBS) H''" ..
  moreover from sc sc' have "ta_seq_consist P vs (llist_of (map NormalAction (OB @ OBS)))"
    by(simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
  moreover from eq eq' sc
  have "eq_upto_seq_inconsist P (map NormalAction (ob @ obs)) (map NormalAction (OB @ OBS)) vs"
    by(simp add: eq_upto_seq_inconsist_appendI)
  ultimately show ?case by blast
qed

lemma heap_clone_cut_and_update:
  assumes hrt: "heap_read_typeable"
  and vs: "vs_conf P h vs"
  and dom_vs: "{(a, al) | al. \<exists>T. P,h \<turnstile> a@al : T} \<subseteq> dom vs"
  and clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and hconf: "hconf h"
  shows "\<exists>obs'' h''. heap_clone P h a h'' \<lfloor>(obs'', a')\<rfloor> \<and>
          ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
          eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction obs'') vs"
using clone
proof cases
  case (ObjClone C h'' FDTs obs')

  note FDTs = `P \<turnstile> C has_fields FDTs`
  let ?als = "map (\<lambda>((F, D), Tm). CField D F) FDTs"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs"
  let ?vs = "mrw_value P vs (NormalAction (NewObj a' C) :: ('addr, 'thread_id) obs_event action)"

  from `P \<turnstile> C has_fields FDTs` have "is_class P C" by(rule has_fields_is_class)
  with `new_obj h C = (h'', \<lfloor>a'\<rfloor>)`
  have type_a': "typeof_addr h'' a' = \<lfloor>Class C\<rfloor>" and hext: "h \<unlhd> h''"
    by(auto dest: new_obj_SomeD hext_new_obj)

  note `heap_copies a a' ?als h'' obs' h'`
  moreover from vs `new_obj h C = (h'', \<lfloor>a'\<rfloor>)`
  have "vs_conf P h'' ?vs" by(rule vs_conf_new_obj)
  moreover {
    have "Pair a ` set ?als \<subseteq> {(a, al) |al. \<exists>T. P,h \<turnstile> a@al : T}"
      using FDTs `typeof_addr h a = \<lfloor>Class C\<rfloor>`
      by(fastforce dest: weak_map_of_SomeI intro: addr_loc_type.intros intro: is_class_type_of.intros simp add: has_field_def)
    also note dom_vs
    also note mrw_value_dom_mono
    finally have "Pair a ` set ?als \<subseteq> dom ?vs" . }
  moreover from hext `typeof_addr h a = \<lfloor>Class C\<rfloor>`
  have "typeof_addr h'' a = \<lfloor>Class C\<rfloor>" by(rule typeof_addr_hext_mono)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> a@al : T) ?als ?Ts" using FDTs
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  moreover from FDTs type_a'
  have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a'@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  moreover from `typeof_addr h a = \<lfloor>Class C\<rfloor>` hconf have "is_class P C"
    by(auto dest: typeof_addr_is_type)
  with `new_obj h C = (h'', \<lfloor>a'\<rfloor>)` hconf have "hconf h''" by(rule hconf_new_obj_mono)
  ultimately
  have "\<exists>obs'' h'''. heap_copies a a' ?als h'' obs'' h''' \<and>
                     ta_seq_consist P ?vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by(rule heap_copies_cut_and_update[OF hrt])
  then obtain obs'' h''' where copies: "heap_copies a a' ?als h'' obs'' h'''"
    and sc: "ta_seq_consist P ?vs (llist_of (map NormalAction obs''))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by blast
  from `typeof_addr h a = \<lfloor>Class C\<rfloor>` `new_obj h C = (h'', \<lfloor>a'\<rfloor>)` FDTs copies
  have "heap_clone P h a h''' \<lfloor>(NewObj a' C # obs'', a')\<rfloor>" by(rule heap_clone.ObjClone)
  moreover from sc have "ta_seq_consist P vs (llist_of (map NormalAction (NewObj a' C # obs'')))" by simp
  moreover from eq have "eq_upto_seq_inconsist P (map NormalAction (NewObj a' C # obs')) (map NormalAction (NewObj a' C # obs'')) vs" by simp
  ultimately show ?thesis unfolding `obs = NewObj a' C # obs'` by blast
next
  case (ArrClone T n h'' FDTs obs')

  note [simp] = `n = array_length h a`
  note FDTs = `P \<turnstile> Object has_fields FDTs`
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs @ replicate n T"
  let ?vs = "mrw_value P vs (NormalAction (NewArr a' T n) :: ('addr, 'thread_id) obs_event action)"

  from `typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` hconf
  have "is_type P (T\<lfloor>\<rceil>)" by(auto dest: typeof_addr_is_type)
  with `new_arr h T n = (h'', \<lfloor>a'\<rfloor>)`
  have type_a': "typeof_addr h'' a' = \<lfloor>Array T\<rfloor>"
    and hext: "h \<unlhd> h''"
    and len: "array_length h'' a' = n"
    by(auto dest: new_arr_SomeD hext_new_arr)

  note `heap_copies a a' ?als h'' obs' h'`
  moreover from vs `new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` `is_type P (T\<lfloor>\<rceil>)`
  have "vs_conf P h'' ?vs" by(rule vs_conf_new_arr)
  moreover {
    have "Pair a ` set ?als \<subseteq> {(a, al) |al. \<exists>T. P,h \<turnstile> a@al : T}"
      using FDTs `typeof_addr h a = \<lfloor>Array T\<rfloor>`
      by(fastforce dest: weak_map_of_SomeI intro: addr_loc_type.intros intro: is_class_type_of.intros simp add: has_field_def)
    also note dom_vs
    also note mrw_value_dom_mono
    finally have "Pair a ` set ?als \<subseteq> dom ?vs" . }
  moreover from hext `typeof_addr h a = \<lfloor>Array T\<rfloor>`
  have type'a: "typeof_addr h'' a = \<lfloor>Array T\<rfloor>"
    and [simp]: "array_length h'' a = array_length h a"
    by(auto intro: hext_arrD)
  from type'a FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a@al : T) ?als ?Ts"
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  moreover from type_a' len FDTs
  have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a'@al : T) ?als ?Ts"
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  moreover from `new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` hconf `is_type P (T\<lfloor>\<rceil>)` have "hconf h''"
    by(rule hconf_new_arr_mono)
  ultimately 
  have "\<exists>obs'' h'''. heap_copies a a' ?als h'' obs'' h''' \<and>
                     ta_seq_consist P ?vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by(rule heap_copies_cut_and_update[OF hrt])
  then obtain obs'' h''' where copies: "heap_copies a a' ?als h'' obs'' h'''"
    and sc: "ta_seq_consist P ?vs (llist_of (map NormalAction obs''))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by blast
  from `typeof_addr h a = \<lfloor>Array T\<rfloor>` `n = array_length h a` `new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` FDTs copies
  have "heap_clone P h a h''' \<lfloor>(NewArr a' T n # obs'', a')\<rfloor>"
    by(rule heap_clone.ArrClone)
  moreover from sc have "ta_seq_consist P vs (llist_of (map NormalAction (NewArr a' T n # obs'')))" by simp
  moreover from eq have "eq_upto_seq_inconsist P (map NormalAction (NewArr a' T n # obs')) (map NormalAction (NewArr a' T n # obs'')) vs" by simp
  ultimately show ?thesis unfolding `obs = NewArr a' T n # obs'` by blast
qed

lemma red_external_cut_and_update:
  fixes final
  assumes hrt: "heap_read_typeable"
  and vs: "vs_conf P (shr s) vs"
  and dom_vs: "{(a, al) | al. \<exists>T. P,shr s \<turnstile> a@al : T} \<subseteq> dom vs"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs'), shr s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>"
  and aok: "final_thread.actions_ok final s t ta"
  and hconf: "hconf (shr s)"
  shows "\<exists>ta'' va'' h''. P,t \<turnstile> \<langle>a\<bullet>M(vs'), shr s\<rangle> -ta''\<rightarrow>ext \<langle>va'', h''\<rangle> \<and> 
                         final_thread.actions_ok final s t ta'' \<and>
                         ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)) \<and>
                         eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) vs"
using red aok
proof(cases)
  case (RedClone obs a')[simp]
  from heap_clone_cut_and_update[OF hrt vs dom_vs `heap_clone P (shr s) a h' \<lfloor>(obs, a')\<rfloor>` hconf]
  show ?thesis using aok
    by(fastforce intro: red_external.RedClone simp add: final_thread.actions_ok_iff)
qed(fastforce intro: red_external.intros simp add: final_thread.actions_ok_iff)+

lemma red_external_aggr_cut_and_update:
  fixes final
  assumes hrt: "heap_read_typeable"
  and vs: "vs_conf P (shr s) vs"
  and dom_vs: "{(a, al) | al. \<exists>T. P,shr s \<turnstile> a@al : T} \<subseteq> dom vs"
  and red: "(ta, va, h') \<in> red_external_aggr P t a M vs' (shr s)"
  and native: "is_native P (the (typeof_addr (shr s) a)) M"
  and aok: "final_thread.actions_ok final s t ta"
  and hconf: "hconf (shr s)"
  shows "\<exists>ta'' va'' h''. (ta'', va'', h'') \<in> red_external_aggr P t a M vs' (shr s) \<and>
                         final_thread.actions_ok final s t ta'' \<and>
                         ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)) \<and>
                         eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) vs"
using red native aok hconf
apply(simp add: red_external_aggr_def final_thread.actions_ok_iff ex_disj_distrib conj_disj_distribR split del: split_if split: split_if_asm disj_split_asm)
   apply(drule (1) heap_clone_cut_and_update[OF hrt vs dom_vs], fastforce)
  apply blast
 apply(auto simp add: is_native.simps external_WT_defs.simps)
done

end

declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]


context allocated_heap begin

lemma heap_copy_loc_allocated_same:
  assumes "heap_copy_loc a a' al h obs h'"
  shows "allocated h' = allocated h"
using assms
by cases(auto del: subsetI simp: heap_write_allocated_same)

lemma heap_copy_loc_allocated_mono:
  "heap_copy_loc a a' al h obs h' \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(simp add: heap_copy_loc_allocated_same)

lemma heap_copies_allocated_same:
  assumes "heap_copies a a' al h obs h'"
  shows "allocated h' = allocated h"
using assms
by(induct)(auto simp add: heap_copy_loc_allocated_same)

lemma heap_copies_allocated_mono:
  "heap_copies a a' al h obs h' \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(simp add: heap_copies_allocated_same)

lemma heap_clone_allocated_mono:
  assumes "heap_clone P h a h' aobs"
  shows "allocated h \<subseteq> allocated h'"
using assms
by cases(blast del: subsetI intro: heap_copies_allocated_mono new_obj_allocated_mono new_arr_allocated_mono intro: subset_trans)+

lemma red_external_allocated_mono:
  assumes "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  shows "allocated h \<subseteq> allocated h'"
using assms
by(cases)(blast del: subsetI intro: heap_clone_allocated_mono heap_write_allocated_same)+

lemma red_external_aggr_allocated_mono:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: split_if_asm dest: heap_clone_allocated_mono sees_method_decl_above elim!: is_class_type_of.cases)

lemma heap_clone_allocatedD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "NewHeapElem a'' x \<in> set obs"
  shows "a'' \<in> allocated h' \<and> a'' \<notin> allocated h"
using assms
by cases(auto dest: new_obj_allocatedD new_arr_allocatedD heap_copies_allocated_mono heap_copies_not_New)

lemma red_external_allocatedD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a' \<in> allocated h' \<and> a' \<notin> allocated h"
by(erule red_external.cases)(auto dest: heap_clone_allocatedD)

lemma red_external_aggr_allocatedD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     is_native P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> a' \<in> allocated h' \<and> a' \<notin> allocated h"
by(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: split_if_asm dest: heap_clone_allocatedD sees_method_decl_above elim!: is_class_type_of.cases)

lemma heap_clone_NewHeapElemD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "ad \<in> allocated h'"
  and "ad \<notin> allocated h"
  shows "\<exists>CTn. NewHeapElem ad CTn \<in> set obs"
using assms
by cases(auto dest!: new_obj_allocatedD new_arr_allocatedD heap_copies_allocated_same)

lemma heap_clone_fail_allocated_same:
  assumes "heap_clone P h a h' None"
  shows "allocated h' = allocated h"
using assms
by(cases)(auto dest: new_obj_allocated_fail new_arr_allocated_fail)

lemma red_external_NewHeapElemD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; a' \<in> allocated h'; a' \<notin> allocated h \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a' CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
by(erule red_external.cases)(auto dest: heap_clone_NewHeapElemD heap_clone_fail_allocated_same)

lemma red_external_aggr_NewHeapElemD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; a' \<in> allocated h'; a' \<notin> allocated h;
     is_native P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a' CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
by(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: split_if_asm dest: heap_clone_fail_allocated_same heap_clone_NewHeapElemD sees_method_decl_above elim!: is_class_type_of.cases)
end

context heap_base begin

lemma binop_known_addrs:
  assumes ok: "start_heap_ok"
  shows "binop bop v1 v2 = \<lfloor>Inl v\<rfloor> \<Longrightarrow> ka_Val v \<subseteq> ka_Val v1 \<union> ka_Val v2 \<union> set start_addrs"
  and "binop bop v1 v2 = \<lfloor>Inr a\<rfloor> \<Longrightarrow> a \<in> ka_Val v1 \<union> ka_Val v2 \<union> set start_addrs"
apply(cases bop, auto split: split_if_asm)[1]
apply(cases bop, auto split: split_if_asm simp add: addr_of_sys_xcpt_start_addr[OF ok])
done

lemma heap_copy_loc_known_addrs_ReadMem:
  assumes "heap_copy_loc a a' al h ob h'"
  and "ReadMem ad al' v \<in> set ob"
  shows "ad = a"
using assms by cases simp

lemma heap_copies_known_addrs_ReadMem:
  assumes "heap_copies a a' als h obs h'"
  and "ReadMem ad al v \<in> set obs"
  shows "ad = a"
using assms
by(induct)(auto dest: heap_copy_loc_known_addrs_ReadMem)

lemma heap_clone_known_addrs_ReadMem:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "ReadMem ad al v \<in> set obs"
  shows "ad = a"
using assms
by cases(auto dest: heap_copies_known_addrs_ReadMem)

lemma red_external_known_addrs_ReadMem:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> {thread_id2addr t, a} \<union> (\<Union>ka_Val ` set vs) \<union> set start_addrs"
by(erule red_external.cases)(simp_all add: heap_clone_known_addrs_ReadMem)

lemma red_external_aggr_known_addrs_ReadMem:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> {thread_id2addr t, a} \<union> (\<Union>ka_Val ` set vs) \<union> set start_addrs"
apply(auto simp add: red_external_aggr_def split: split_if_asm dest: heap_clone_known_addrs_ReadMem)
done

lemma heap_copy_loc_known_addrs_WriteMem:
  assumes "heap_copy_loc a a' al h ob h'"
  and "ob ! n = WriteMem ad al' (Addr a'')" "n < length ob"
  shows "a'' \<in> new_obs_addrs (take n ob)"
using assms
by cases(auto simp add: nth_Cons new_obs_addrs_def split: nat.split_asm)

lemma heap_copies_known_addrs_WriteMem:
  assumes "heap_copies a a' als h obs h'"
  and "obs ! n = WriteMem ad al (Addr a'')" "n < length obs"
  shows "a'' \<in> new_obs_addrs (take n obs)"
using assms
by(induct arbitrary: n)(auto simp add: nth_append new_obs_addrs_def dest: heap_copy_loc_known_addrs_WriteMem split: split_if_asm)

lemma heap_clone_known_addrs_WriteMem:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "obs ! n = WriteMem ad al (Addr a'')" "n < length obs"
  shows "a'' \<in> new_obs_addrs (take n obs)"
using assms
by cases(auto simp add: nth_Cons new_obs_addrs_def split: nat.split_asm dest: heap_copies_known_addrs_WriteMem)

lemma red_external_known_addrs_WriteMem:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a'); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a' \<in> {thread_id2addr t, a} \<union> (\<Union>ka_Val ` set vs) \<union> set start_addrs \<union> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
by(erule red_external.cases)(auto dest: heap_clone_known_addrs_WriteMem)

lemma red_external_aggr_known_addrs_WriteMem:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a'); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a' \<in> {thread_id2addr t, a} \<union> (\<Union>ka_Val ` set vs) \<union> set start_addrs \<union> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
apply(auto simp add: red_external_aggr_def split: split_if_asm dest: heap_clone_known_addrs_WriteMem)
done

lemma red_external_known_addrs_mono:
  assumes ok: "start_heap_ok"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  shows "(case va of RetVal v \<Rightarrow> ka_Val v | RetExc a \<Rightarrow> {a} | RetStaySame \<Rightarrow> {}) \<subseteq> {thread_id2addr t, a} \<union> (\<Union>ka_Val ` set vs) \<union> set start_addrs \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using red
by cases(auto simp add: addr_of_sys_xcpt_start_addr[OF ok] new_obs_addrs_def heap_clone.simps)

lemma red_external_aggr_known_addrs_mono:
  assumes ok: "start_heap_ok"
  and red: "(ta, va, h') \<in> red_external_aggr P t a M vs h" "is_native P (the (typeof_addr h a)) M"
  shows "(case va of RetVal v \<Rightarrow> ka_Val v | RetExc a \<Rightarrow> {a} | RetStaySame \<Rightarrow> {}) \<subseteq> {thread_id2addr t, a} \<union> (\<Union>ka_Val ` set vs) \<union> set start_addrs \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using red
apply(auto simp add: red_external_aggr_def addr_of_sys_xcpt_start_addr[OF ok] new_obs_addrs_def heap_clone.simps split: split_if_asm)
apply(auto simp add: is_native.simps elim!: external_WT_defs.cases is_class_type_of.cases dest: sees_method_decl_above)
done

lemma red_external_NewThread_idD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> t' = addr2thread_id a \<and> a' = a"
by(erule red_external.cases) simp_all

lemma red_external_aggr_NewThread_idD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; 
     NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> t' = addr2thread_id a \<and> a' = a"
apply(auto simp add: red_external_aggr_def split: split_if_asm)
done

end

end
