(*  Title:      JinjaThreads/MM/JMM_Common.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{JMM Instantiation with Jinja -- common parts} *}

theory JMM_Common imports
  JMM_Type
  SC_Completion
  "../Framework/FWInitFinLift"
begin

section {* JMM traces for Jinja semantics *}

context \<tau>multithreaded begin

inductive_set \<E> :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> 'o) llist set"
  for \<sigma> :: "('l,'t,'x,'m,'w) state"
where
  "mthr.Runs \<sigma> E'
  \<Longrightarrow> lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) \<in> \<E> \<sigma>"

lemma actions_\<E>E_aux:
  fixes \<sigma> E'
  defines "E == lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
  assumes mthr: "mthr.Runs \<sigma> E'"
  and a: "Fin a < llength E"
  obtains m n t ta
  where "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
  and "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and "Fin m < tlength E'"
  and "a = (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
  and "tnth E' m = (t, ta)"
proof -
  from lnth_lconcat_conv[OF a[unfolded E_def], folded E_def]
  obtain m n
    where "lnth E a = lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) m) n"
    and "Fin n < llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) m)"
    and "Fin m < llength (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
    and "Fin a = (\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) + Fin n"
    by blast
  moreover
  obtain t ta where "tnth E' m = (t, ta)" by(cases "tnth E' m")
  ultimately have E_a: "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
    and n: "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and m: "Fin m < tlength E'"
    and a: "Fin a = (\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) + Fin n"
    by(simp_all add: lnth_llist_of)
  note a
  also have "(\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) = 
            setsum (Fin \<circ> (\<lambda>i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) {..<m}"
    using m by(simp add: less_trans[where y="Fin m"] split_beta)
  also have "\<dots> = Fin (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
    by(subst setsum_hom)(simp_all add: zero_inat_def)
  finally have a: "a = (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n" by simp
  with E_a n m show thesis using `tnth E' m = (t, ta)` by(rule that)
qed

lemma actions_\<E>E:
  assumes E: "E \<in> \<E> \<sigma>"
  and a: "Fin a < llength E"
  obtains E' m n t ta
  where "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
  and "mthr.Runs \<sigma> E'"
  and "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
  and "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and "Fin m < tlength E'"
  and "a = (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
  and "tnth E' m = (t, ta)"
proof -
  from E obtain E' ws
    where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
    and "mthr.Runs \<sigma> E'" by(rule \<E>.cases) blast
  from `mthr.Runs \<sigma> E'` a[unfolded E]
  show ?thesis
    by(rule actions_\<E>E_aux)(fold E, rule that[OF E `mthr.Runs \<sigma> E'`])
qed

end

lemma convert_RA_not_write:
  "ob \<in> set (convert_RA ln) \<Longrightarrow> \<not> is_write_action (NormalAction ob)"
by(auto simp add: convert_RA_def)

lemma ta_seq_consist_convert_RA:
  "ta_seq_consist P vs (llist_of ((map NormalAction \<circ> convert_RA) ln))"
proof(rule ta_seq_consist_nthI)
  fix i ad al v
  assume "Fin i < llength (llist_of ((map NormalAction \<circ> convert_RA) ln))"
    and "lnth (llist_of ((map NormalAction \<circ> convert_RA) ln)) i = NormalAction (ReadMem ad al v)"
  hence "ReadMem ad al v \<in> set (convert_RA ln)"
    by(auto simp add: in_set_conv_nth)
  hence False by(auto simp add: convert_RA_def)
  thus "\<exists>b. mrw_values P vs (list_of (ltake (Fin i) (llist_of ((map NormalAction \<circ> convert_RA) ln)))) (ad, al) = \<lfloor>(v, b)\<rfloor>" ..
qed

section {* Properties of external calls *}

context heap_base begin

lemma heap_clone_None_dom_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and clone: "heap_clone P h a h' None"
  shows "dom (typeof_addr h') = dom (typeof_addr h)"
using clone
by(cases)(auto dest: heap_ops_typeof_minimalD[OF minimal] del: equalityI)

lemma heap_copy_loc_dom_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and copy: "heap_copy_loc a a' al h ob h'"
  shows "dom (typeof_addr h') = dom (typeof_addr h)"
using copy
by cases(auto dest: heap_ops_typeof_minimalD[OF minimal] del: equalityI)

lemma heap_copies_dom_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and copies: "heap_copies a a' als h obs h'"
  shows "dom (typeof_addr h') = dom (typeof_addr h)"
using copies
by induct(auto dest: heap_copy_loc_dom_typeof_addrD[OF minimal] del: equalityI)

lemma heap_clone_Some_dom_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  shows "dom (typeof_addr h') = insert a' (dom (typeof_addr h))"
using clone
by cases(auto del: equalityI dest!: heap_copies_dom_typeof_addrD[OF minimal] heap_ops_typeof_minimalD[OF minimal])

end

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

lemma heap_clone_typeof_addrD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  shows "typeof_addr h a' = None" 
  and "NewHeapElem a'' x \<in> set obs \<Longrightarrow> a'' = a' \<and> typeof_addr h' a' = Some (ty_of_htype x)"
using assms
by(fastsimp elim!: heap_clone.cases dest: new_obj_SomeD new_arr_SomeD hext_heap_copies heap_copies_not_New elim: hext_objD hext_arrD)+

lemma heap_clone_array_lengthD:
  "\<lbrakk> heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>; NewArr a'' T n \<in> set obs \<rbrakk>
  \<Longrightarrow> array_length h' a'' = n"
by(fastsimp elim!: heap_clone.cases dest: new_arr_SomeD hext_heap_copies heap_copies_not_New[where x="Array_type T n"] hext_arrD(2))

lemma red_external_New_typeof_addrD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h a' = None \<and> typeof_addr h' a' = Some (ty_of_htype x)"
by(erule red_external.cases)(auto dest: heap_clone_typeof_addrD)

lemma red_external_NewArr_lengthD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewArr a' T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length h' a' = n"
by(erule red_external.cases)(auto dest: heap_clone_array_lengthD)

lemma heap_clone_New_same_addr_same:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "obs ! i = NewHeapElem a'' x" "i < length obs"
  and "obs ! j = NewHeapElem a'' x'" "j < length obs"
  shows "i = j"
using assms
apply cases
apply(fastsimp simp add: nth_Cons' gr0_conv_Suc in_set_conv_nth split: split_if_asm dest: heap_copies_not_New)+
done

lemma red_external_New_same_addr_same:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; 
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a' x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a' x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(auto elim!: red_external.cases simp add: nth_Cons' split: split_if_asm dest: heap_clone_New_same_addr_same)


lemma heap_clone_None_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and clone: "heap_clone P h a h' None"
  shows "typeof_addr h' = typeof_addr h"
using clone
by(cases)(auto dest: heap_ops_typeof_minimalD'[OF minimal])

lemma heap_copy_loc_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and copy: "heap_copy_loc a a' al h ob h'"
  shows "typeof_addr h' = typeof_addr h"
using copy
by cases(auto dest: heap_ops_typeof_minimalD'[OF minimal])

lemma heap_copies_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and copies: "heap_copies a a' als h obs h'"
  shows "typeof_addr h' = typeof_addr h"
using copies
by induct(auto dest: heap_copy_loc_typeof_addrD[OF minimal])

lemma heap_clone_new_heap_ops_obs:
  assumes minimal: "heap_ops_typeof_minimal"
  and clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  shows 
  "\<lbrakk> typeof_addr h' a'' = \<lfloor>T\<rfloor>; typeof_addr h a'' = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a'' CTn \<in> set obs \<and> ty_of_htype CTn = T \<and> h' \<turnstile>a a'' : CTn"
using clone
apply cases
 apply(drule heap_copies_typeof_addrD[OF minimal])
 apply(frule heap_ops_typeof_minimalD'[OF minimal])
 apply(drule new_obj_SomeD)
 apply(auto split: split_if_asm)[1]

apply(frule hext_heap_copies)
apply(drule heap_copies_typeof_addrD[OF minimal])
apply(frule heap_ops_typeof_minimalD'[OF minimal])
apply(drule new_arr_SomeD)
apply(clarsimp split: split_if_asm)
apply(rule exI)
apply(rule conjI)
 apply(rule disjI1)
 apply(rule refl)
apply simp
apply(drule hext_arrD(2)[where a=a'])
 apply simp
apply simp
done

lemma red_external_new_heap_ops_obs:
  assumes minimal: heap_ops_typeof_minimal
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  shows
  "\<lbrakk> typeof_addr h' a' = Some T; typeof_addr h a' = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a' CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> h' \<turnstile>a a' : CTn"
using red
apply cases
apply (auto dest: heap_ops_typeof_minimalD[OF minimal] heap_clone_None_typeof_addrD[OF minimal] heap_clone_new_heap_ops_obs[OF minimal])
done

lemma heap_copy_loc_read_addrD:
  assumes "heap_copy_loc a a' al h ob h'"
  and "ReadMem ad al' v \<in> set ob"
  shows "ad = a"
using assms by cases auto

lemma heap_copies_read_addrD:
  assumes "heap_copies a a' als h obs h'"
  and "ReadMem ad al v \<in> set obs"
  shows "ad = a"
using assms by induct (auto dest: heap_copy_loc_read_addrD)

lemma heap_clone_read_addrD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "ReadMem ad al v \<in> set obs"
  shows "ad = a"
using assms by cases(auto dest: heap_copies_read_addrD)

lemma red_external_read_addrD:
  assumes "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> {t, a} \<union> {a. Addr a \<in> set vs} \<union> set start_addrs"
using assms by cases(auto dest: heap_clone_read_addrD)


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
    by(fastsimp intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  ultimately have "ad = a \<and> al \<in> set ?als" by(rule heap_copies_read_typeable)
  hence [simp]: "ad = a" and "al \<in> set ?als" by simp_all
  then obtain F D T where [simp]: "al = CField D F" and "((F, D), T) \<in> set FDTs" by auto
  with type `h \<unlhd> H'` `typeof_addr h a = \<lfloor>Class C\<rfloor>` show ?thesis 
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp elim!: ballE[where x="((F, D), T)"] addr_loc_type.cases dest: typeof_addr_hext_mono intro: addr_loc_type.intros)
next
  case (ArrClone T n H' obs')
  let ?als = "map ACell [0..<n]"
  let ?Ts = "replicate n T"
  note `heap_copies a a' ?als H' obs' h'`
  moreover from `obs = NewArr a' T n # obs'` read
  have "ReadMem ad al v \<in> set obs'" by simp
  moreover from `new_arr h T n = (H', \<lfloor>a'\<rfloor>)`
  have "h \<unlhd> H'" by(rule hext_new_arr)
  with `typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `n = array_length h a`
  have "typeof_addr H' a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>" "array_length H' a = n"
    by(auto dest: typeof_addr_hext_mono hext_arrD)
  hence type: "list_all2 (\<lambda>al T. P,H' \<turnstile> a@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI addr_loc_type.intros)
  ultimately have "ad = a \<and> al \<in> set ?als" by(rule heap_copies_read_typeable)
  hence [simp]: "ad = a" and "al \<in> set ?als" by simp_all
  then obtain n' where [simp]: "al = ACell n'" and "n' < n" by auto
  with type `h \<unlhd> H'` `typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `n = array_length h a`
  show ?thesis
    by(fastsimp dest: list_all2_nthD[where p=n'] elim: addr_loc_type.cases dest: typeof_addr_hext_mono intro: addr_loc_type.intros)
qed

lemma red_external_read_mem_typeable:
  assumes wf: "wf_prog wfmd P"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T'. P,h \<turnstile> ad@al : T'"
using red read
by cases(auto dest: heap_clone_read_typeable intro: addr_loc_type.intros wf_sub_Thread_has_interrupted_flag[OF wf])

end

context heap_conf_read begin

lemma heap_copy_loc_write_typeable:
  assumes "heap_copy_loc ad ad' al h obs h'"
  and "WriteMem ad'' al'' v \<in> set obs"
  and "hconf h"
  and "P,h \<turnstile> ad@al : T" "P,h \<turnstile> ad'@al : T"
  shows "\<exists>T'. P,h' \<turnstile> ad''@al'' : T' \<and> P,h' \<turnstile> v :\<le> T'"
using assms
by cases(auto dest!: heap_read_conf hext_heap_write intro: addr_loc_type_hext_mono conf_hext)

lemma heap_copies_write_typeable:
  assumes "heap_copies ad ad' als h obs h'"
  and "WriteMem ad'' al'' v \<in> set obs"
  and "hconf h"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts" 
  and "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts"
  shows "\<exists>T'. P,h' \<turnstile> ad''@al'' : T' \<and> P,h' \<turnstile> v :\<le> T'"
using assms
proof(induct arbitrary: Ts)
  case Nil thus ?case by simp
next
  case (Cons al h ob h' als obs h'')
  note copy = `heap_copy_loc ad ad' al h ob h'`
  from `list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) (al # als) Ts`
  obtain T Ts' where Ts: "Ts = T # Ts'"
    and alT: "P,h \<turnstile> ad@al : T" 
    and als: "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from `list_all2 (addr_loc_type P h ad') (al # als) Ts` Ts
  have alT': "P,h \<turnstile> ad'@al : T"
    and als': "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts'" by simp_all

  from `WriteMem ad'' al'' v \<in> set (ob @ obs)`
  have "WriteMem ad'' al'' v \<in> set ob \<or> WriteMem ad'' al'' v \<in> set obs" by simp
  thus ?case
  proof
    assume "WriteMem ad'' al'' v \<in> set ob"
    with copy have "\<exists>T'. P,h' \<turnstile> ad''@al'' : T' \<and> P,h' \<turnstile> v :\<le> T'"
      using `hconf h` alT alT' by(rule heap_copy_loc_write_typeable)
    moreover from `heap_copies ad ad' als h' obs h''`
    have "h' \<unlhd> h''" by(rule hext_heap_copies)
    ultimately show ?thesis by(auto intro: conf_hext addr_loc_type_hext_mono)
  next
    assume "WriteMem ad'' al'' v \<in> set obs"
    moreover from copy `hconf h` alT alT'
    have "hconf h'" by(rule hconf_heap_copy_loc_mono)
    moreover from copy have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
    with als have "list_all2 (\<lambda>al T. P,h' \<turnstile> ad@al : T) als Ts'"
      by -(erule list_all2_mono[OF _ addr_loc_type_hext_mono])
    moreover from als' `h \<unlhd> h'` have "list_all2 (\<lambda>al T. P,h' \<turnstile> ad'@al : T) als Ts'"
      by -(erule list_all2_mono[OF _ addr_loc_type_hext_mono])
    ultimately show ?thesis by(rule Cons.hyps)
  qed
qed

lemma heap_clone_write_typeable:
  assumes wf: "wf_prog wfmd P"
  and clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "write": "WriteMem ad al v \<in> set obs"
  and hconf: "hconf h"
  shows "\<exists>T'. P,h' \<turnstile> ad@al : T' \<and> P,h' \<turnstile> v :\<le> T'"
using clone
proof cases
  case (ObjClone C h'' FDTs obs')
  note FDTs = `P \<turnstile> C has_fields FDTs`
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs"
  let ?Ts = "map (fst \<circ> snd) FDTs"
  note `heap_copies a a' ?als h'' obs' h'` 
  moreover from "write" `obs = NewObj a' C # obs'`
  have "WriteMem ad al v \<in> set obs'" by simp
  moreover from `typeof_addr h a = \<lfloor>Class C\<rfloor>` `hconf h` have "is_class P C"
    by(auto dest: typeof_addr_is_type)
  from `new_obj h C = (h'', \<lfloor>a'\<rfloor>)` have "h \<unlhd> h''" "hconf h''"
    by(rule hext_heap_ops hconf_new_obj_mono[OF _ `hconf h` `is_class P C`])+
  note `hconf h''` 
  moreover from wf FDTs have "distinct (map fst FDTs)"
    by(rule has_fields_distinct)
  with `typeof_addr h a = \<lfloor>Class C\<rfloor>` FDTs
  have "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro!: addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> a@al : T) ?als ?Ts"
    by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h''`])
  moreover from `new_obj h C = (h'', \<lfloor>a'\<rfloor>)`
  have "typeof_addr h'' a' = \<lfloor>Class C\<rfloor>" by(auto dest: new_obj_SomeD)
  with FDTs `distinct (map fst FDTs)`
  have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a'@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro!: addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
  ultimately show ?thesis by(rule heap_copies_write_typeable)
next
  case (ArrClone T n h'' obs')
  note [simp] = `n = array_length h a`
  let ?als = "map ACell [0..<n]"
  let ?Ts = "replicate n T"
  note `heap_copies a a' (map ACell [0..<n]) h'' obs' h'`
  moreover from "write" `obs = NewArr a' T n # obs'`
  have "WriteMem ad al v \<in> set obs'" by simp
  moreover from `typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `hconf h` have "is_type P T"
    by(auto dest: typeof_addr_is_type)
  from `new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` have "h \<unlhd> h''" "hconf h''"
    by(rule hext_heap_ops hconf_new_arr_mono[OF _ `hconf h` `is_type P T`])+
  note `hconf h''`
  moreover from `h \<unlhd> h''` `typeof_addr h a = \<lfloor>Array T\<rfloor>`
  have type'a: "typeof_addr h'' a = \<lfloor>Array T\<rfloor>"
    and [simp]: "array_length h'' a = array_length h a" by(auto intro: hext_arrD)
  from type'a have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI addr_loc_type.intros)
  moreover from `new_arr h T n = (h'', \<lfloor>a'\<rfloor>)`
  have "typeof_addr h'' a' = \<lfloor>Array T\<rfloor>" "array_length h'' a' = array_length h a"
    by(auto dest: new_arr_SomeD)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> a'@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI addr_loc_type.intros)
  ultimately show ?thesis by(rule heap_copies_write_typeable)
qed

lemma red_external_write_typeable:
  assumes wf_prog: "wf_prog wfmd P"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and "write": "WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and hconf: "hconf h"
  shows "\<exists>T'. P,h' \<turnstile> ad@al : T' \<and> P,h' \<turnstile> v :\<le> T'"
using red "write" hconf
apply cases
apply(fastsimp elim: typeof_addr_hext_mono[OF hext_heap_write] intro: addr_loc_type.intros wf_sub_Thread_has_interrupted_flag[OF wf_prog] heap_clone_write_typeable[OF wf_prog])+
done

end

context heap begin

lemma mrw_values_start_heap_obs_typeable:
  assumes "mrw_values P empty (map NormalAction start_heap_obs) (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,start_heap \<turnstile> ad@al : T \<and> P,start_heap \<turnstile> v :\<le> T"
proof -
  from mrw_values_eq_SomeD[OF assms]
  obtain obs' wa obs'' 
    where eq: "map NormalAction start_heap_obs = obs' @ wa # obs''"
    and "is_write_action wa"
    and adal: "(ad, al) \<in> action_loc_aux P wa"
    and vwa: "value_written_aux P wa al = v"
    by blast
  from `is_write_action wa` show ?thesis
  proof cases
    case (WriteMem ad' al' v')
    with vwa adal eq have "WriteMem ad al v \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv)
    thus ?thesis by(rule start_heap_write_typeable)
  next
    case (NewObj ad' C)
    with vwa adal eq have "NewObj ad C \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv)
    hence "typeof_addr start_heap ad = \<lfloor>Class C\<rfloor>" by(rule NewObj_start_heap_obsD)
    thus ?thesis using adal vwa NewObj
      by(fastsimp simp add: has_field_def intro: addr_loc_type.intros)
  next
    case (NewArr ad' T n)
    with vwa adal eq have "NewArr ad T n \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv)
    hence "typeof_addr start_heap ad = \<lfloor>Array T\<rfloor>"
      and "array_length start_heap ad = n" by(rule NewArr_start_heap_obsD)+
    thus ?thesis using adal vwa NewArr by(auto intro: addr_loc_type.intros)
  qed
qed

end

section {* Cut and update for external calls *}

declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

lemma heap_copy_loc_cut_and_update:
  assumes vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile>jmm' ad@al : T \<and> P,h \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,h \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and type: "P,h \<turnstile>jmm' a@al : T" "P,h \<turnstile>jmm' a'@al : T"
  shows "\<exists>obs'' h''. jmm'_heap_copy_loc P a a' al h obs'' h'' \<and>
                     ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction [ReadMem a al v, WriteMem a' al v]) (map NormalAction obs'') vs"
proof -
  from type(1) have "(a, al) \<in> dom vs" using dom_vs by blast
  then obtain v' b where v'b: "vs (a, al) = \<lfloor>(v', b)\<rfloor>" by auto
  from vs[OF this] type have conf: "P,h \<turnstile>jmm' v' :\<le> T" by(auto dest: jmm'.addr_loc_type_fun)
  let ?obs'' = "[ReadMem a al v', WriteMem a' al v']"
  from type(1) conf have "jmm_heap_read' P h a al v'"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  moreover from jmm'.heap_write_total[OF type(2) conf] 
  obtain h'' where "jmm_heap_write' P h a' al v' h''" ..
  ultimately have "jmm'_heap_copy_loc P a a' al h ?obs'' h''" ..
  moreover have "ta_seq_consist P vs (llist_of (map NormalAction ?obs''))"
    using v'b by simp
  moreover have "eq_upto_seq_inconsist P (map NormalAction [ReadMem a al v, WriteMem a' al v]) (map NormalAction ?obs'') vs"
    using v'b by(simp)
  ultimately show ?thesis by blast
qed

lemma eq_upto_seq_inconsist_appendI:
  "\<lbrakk> eq_upto_seq_inconsist P obs OBS vs;
     \<lbrakk> ta_seq_consist P vs (llist_of obs) \<rbrakk> \<Longrightarrow> eq_upto_seq_inconsist P obs' OBS' (mrw_values P vs OBS) \<rbrakk>
  \<Longrightarrow> eq_upto_seq_inconsist P (obs @ obs') (OBS @ OBS') vs"
apply(induct obs arbitrary: vs OBS)
 apply simp
apply(auto simp add: eq_upto_seq_inconsist_Cons1)
apply(simp split: action.split obs_event.split)
apply auto
done

lemma heap_copies_cut_and_update:
  assumes copies: "jmm'_heap_copies P a a' als h obs h'"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile>jmm' ad@al : T \<and> P,h \<turnstile>jmm' v :\<le> T"
    (is "PROP ?vs vs h")
  and dom_vs: "{(ad, al). \<exists>T. P,h \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and type1: "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a@al : T) als Ts"
  and type2: "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a'@al : T) als Ts"
  and hconf: "P \<turnstile>jmm' h \<surd>"
  shows "\<exists>obs'' h''. jmm'_heap_copies P a a' als h obs'' h'' \<and>
                     ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction obs'') vs"
    (is "?concl als h obs vs")
using assms
proof(induct arbitrary: h Ts vs)
  case Nil thus ?case by(auto intro: jmm'.heap_copies.Nil)
next
  case (Cons al H ob h' als obs h'' h Ts vs)
  note vs = `PROP ?vs vs h`
    and dom_vs = `{(ad, al). \<exists>T. P,h \<turnstile>jmm' ad@al : T} \<subseteq> dom vs`
  note type1 = `list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a@al : T) (al # als) Ts`
    and type2 = `list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a'@al : T) (al # als) Ts`
  note hconf = `P \<turnstile>jmm' h \<surd>`

  from type1 obtain T Ts' where Ts: "Ts = T # Ts'"
    and type1': "P,h \<turnstile>jmm' a@al : T"
    and type1'': "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from type2 Ts have type2': "P,h \<turnstile>jmm' a'@al : T"
    and type2'': "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a'@al : T) als Ts'"
    by simp_all
  from `jmm'_heap_copy_loc P a a' al H ob h'`
  obtain v where "ob = [ReadMem a al v, WriteMem a' al v]" by cases
  with heap_copy_loc_cut_and_update[OF vs dom_vs type1' type2', where ?b1="\<lambda>_ _ _ b. b" and v=v]
  obtain OB H' where hcl: "jmm'_heap_copy_loc P a a' al h OB H'"
    and sc: "ta_seq_consist P vs (llist_of (map NormalAction OB))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction ob) (map NormalAction OB) vs" by auto
  from hcl have hext: "h \<unlhd>jmm' H'" by(rule jmm'.hext_heap_copy_loc)

  let ?vs' = "mrw_values P vs (map NormalAction OB)"
  have "PROP ?vs ?vs' H'"
  proof -
    fix ad al v b
    assume vs': "?vs' (ad, al) = \<lfloor>(v, b)\<rfloor>"
    show "\<exists>T. P,H' \<turnstile>jmm' ad@al : T \<and> P,H' \<turnstile>jmm' v :\<le> T"
    proof(cases "vs (ad, al) = \<lfloor>(v, b)\<rfloor>")
      case True 
      from hext vs[OF True] show ?thesis
        by(auto intro: jmm'.addr_loc_type_hext_mono jmm'.conf_hext)
    next
      case False
      with mrw_values_eq_SomeD[OF vs']
      obtain obs' wa obs'' 
        where eq: "map NormalAction OB = obs' @ wa # obs''"
        and "is_write_action wa"
        and adal: "(ad, al) \<in> action_loc_aux P wa"
        and vwa: "value_written_aux P wa al = v"
        by blast
      with hcl have "\<not> is_new_action wa"
        by(auto simp add: map_eq_append_conv elim!: is_new_action.cases dest: jmm'.heap_copy_loc_not_New)
      with `is_write_action wa` adal vwa have "wa = NormalAction (WriteMem ad al v)"
        by cases auto
      with eq have "WriteMem ad al v \<in> set OB" by(auto simp add: map_eq_append_conv)
      with hcl show ?thesis using hconf type1' type2' by(rule jmm'.heap_copy_loc_write_typeable)
    qed
  qed
  moreover
  from jmm'.heap_copy_loc_typeof_addrD[OF jmm'_heap_ops_typeof_minimal hcl]
    mrw_values_dom_mono[where vs=vs and P=P and obs="map NormalAction OB"] dom_vs jmm'.hext_arrD(2)[OF hext]
  have "{(ad, al). \<exists>T. P,H' \<turnstile>jmm' ad@al : T} \<subseteq> dom ?vs'"
    by(fastsimp elim: jmm'.addr_loc_type.cases subsetD intro: jmm'.addr_loc_type.intros iff del: domIff)
  moreover from type1'' have "list_all2 (\<lambda>al T. P,H' \<turnstile>jmm' a@al : T) als Ts'"
    by(rule list_all2_mono)(rule jmm'.addr_loc_type_hext_mono[OF _ hext])
  moreover from type2'' have "list_all2 (\<lambda>al T. P,H' \<turnstile>jmm' a'@al : T) als Ts'"
    by(rule list_all2_mono)(rule jmm'.addr_loc_type_hext_mono[OF _ hext])
  moreover from hcl hconf type1' type2'
  have "P \<turnstile>jmm' H' \<surd>" by(rule jmm'.hconf_heap_copy_loc_mono)
  ultimately have "?concl als H' obs ?vs'" by(rule Cons.hyps)
  then obtain OBS H''
    where copies: "jmm'_heap_copies P a a' als H' OBS H''"
    and sc': "ta_seq_consist P ?vs' (llist_of (map NormalAction OBS))"
    and eq': "eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction OBS) ?vs'" by blast
  from hcl copies have "jmm'_heap_copies P a a' (al#als) h (OB @ OBS) H''" ..
  moreover from sc sc' have "ta_seq_consist P vs (llist_of (map NormalAction (OB @ OBS)))"
    by(simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
  moreover from eq eq' sc
  have "eq_upto_seq_inconsist P (map NormalAction (ob @ obs)) (map NormalAction (OB @ OBS)) vs"
    by(simp add: eq_upto_seq_inconsist_appendI)
  ultimately show ?case by blast
qed

lemma heap_clone_cut_and_update:
  assumes wf: "wf_prog wf_md P"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile>jmm' ad@al : T \<and> P,h \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,h \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and clone: "jmm'_heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and hconf: "P \<turnstile>jmm' h \<surd>"
  shows "\<exists>obs'' h''. jmm'_heap_clone P h a h'' \<lfloor>(obs'', a')\<rfloor> \<and>
          ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
          eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction obs'') vs"
using clone
proof cases
  case (ObjClone C h'' FDTs obs')
  
  note FDTs = `P \<turnstile> C has_fields FDTs`
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs"
  let ?Ts = "map (fst \<circ> snd) FDTs"
  let ?vs = "mrw_value P vs (NormalAction (NewObj a' C))"

  from `jmm_new_obj h C = (h'', \<lfloor>a'\<rfloor>)`
  have type_a': "jmm_typeof_addr h'' a' = \<lfloor>Class C\<rfloor>"
    and hext: "h \<unlhd>jmm' h''"
    and dom_typeof: "dom (jmm_typeof_addr h'') = insert a' (dom (jmm_typeof_addr h))"
    and type_a'': "jmm_typeof_addr h a' = None"
    by(auto dest: jmm'.new_obj_SomeD jmm'.hext_new_obj jmm'.heap_ops_typeof_minimalD[OF jmm'_heap_ops_typeof_minimal] del: subsetI)

  note `jmm'_heap_copies P a a' ?als h'' obs' h'`
  moreover {
    fix ad al v b
    assume "?vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
    hence "\<exists>T. P,h'' \<turnstile>jmm' ad@al : T \<and> P,h'' \<turnstile>jmm' v :\<le> T"
      using FDTs type_a' hext
      apply(auto split: split_if_asm)
      prefer 4
      apply(fastsimp simp add: has_field_def dest: has_fields_fun vs intro: jmm'.addr_loc_type.intros elim: jmm'.addr_loc_type_hext_mono jmm'.conf_hext)
      apply(fastsimp simp add: has_field_def dest: has_fields_fun vs intro: jmm'.addr_loc_type.intros elim: jmm'.addr_loc_type_hext_mono jmm'.conf_hext notE)+
      done }
  moreover { fix ad al T
    assume adal: "P,h'' \<turnstile>jmm' ad@al : T"
    have "(ad, al) \<in> dom ?vs"
    proof(cases "\<exists>T. P,h \<turnstile>jmm' ad@al : T")
      case True
      with dom_vs[THEN subsetD, of "(ad, al)"]
      have "(ad, al) \<in> dom vs" by auto
      also note mrw_value_dom_mono
      finally show ?thesis .
    next
      case False
      have "ad = a'" using False adal dom_typeof[THEN equalityD1, THEN subsetD, of ad] hext
        by(fastsimp elim: jmm'.addr_loc_type.cases dest: jmm'.typeof_addr_hext_mono jmm'.hext_arrD(2)[OF hext] intro: jmm'.addr_loc_type.intros)+
      with adal type_a' show ?thesis by cases fastsimp+
    qed }
  hence "{(ad, al). \<exists>T. P,h'' \<turnstile>jmm' ad@al : T} \<subseteq> dom ?vs" by blast
  moreover from wf FDTs have "distinct (map fst FDTs)"
    by(rule has_fields_distinct)
  with `jmm_typeof_addr h a = \<lfloor>Class C\<rfloor>` FDTs
  have "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro!: jmm'.addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile>jmm' a@al : T) ?als ?Ts"
    by(rule list_all2_mono)(rule jmm'.addr_loc_type_hext_mono[OF _ hext])
  moreover from FDTs `distinct (map fst FDTs)` type_a'
  have "list_all2 (\<lambda>al T. P,h'' \<turnstile>jmm' a'@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro!: jmm'.addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
  moreover from `jmm_typeof_addr h a = \<lfloor>Class C\<rfloor>` hconf have "is_class P C"
    by(auto dest: jmm'.typeof_addr_is_type)
  with `jmm_new_obj h C = (h'', \<lfloor>a'\<rfloor>)` hconf have "P \<turnstile>jmm' h'' \<surd>"
    by(rule jmm'.hconf_new_obj_mono)
  ultimately
  have "\<exists>obs'' h'''. jmm'_heap_copies P a a' ?als h'' obs'' h''' \<and>
                     ta_seq_consist P ?vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by(rule heap_copies_cut_and_update)
  then obtain obs'' h''' where copies: "jmm'_heap_copies P a a' ?als h'' obs'' h'''"
    and sc: "ta_seq_consist P ?vs (llist_of (map NormalAction obs''))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by blast
  from `jmm_typeof_addr h a = \<lfloor>Class C\<rfloor>` `jmm_new_obj h C = (h'', \<lfloor>a'\<rfloor>)` FDTs copies
  have "jmm'_heap_clone P h a h''' \<lfloor>(NewObj a' C # obs'', a')\<rfloor>"
    by(rule jmm'.heap_clone.ObjClone)
  moreover from sc have "ta_seq_consist P vs (llist_of (map NormalAction (NewObj a' C # obs'')))" by simp
  moreover from eq have "eq_upto_seq_inconsist P (map NormalAction (NewObj a' C # obs')) (map NormalAction (NewObj a' C # obs'')) vs" by simp
  ultimately show ?thesis unfolding `obs = NewObj a' C # obs'` by blast
next
  case (ArrClone T n h'' obs')

  note [simp] = `n = jmm_array_length h a`
  let ?als = "map ACell [0..<n]"
  let ?Ts = "replicate n T"
  let ?vs = "mrw_value P vs (NormalAction (NewArr a' T n))"

  from `jmm_new_arr h T n = (h'', \<lfloor>a'\<rfloor>)`
  have type_a': "jmm_typeof_addr h'' a' = \<lfloor>Array T\<rfloor>"
    and hext: "h \<unlhd>jmm' h''"
    and dom_typeof: "dom (jmm_typeof_addr h'') = insert a' (dom (jmm_typeof_addr h))"
    and type_a'': "jmm_typeof_addr h a' = None"
    and len: "jmm_array_length h'' a' = n"
    by(auto dest: jmm'.new_arr_SomeD jmm'.hext_new_arr jmm'.heap_ops_typeof_minimalD[OF jmm'_heap_ops_typeof_minimal] del: subsetI)

  note `jmm'_heap_copies P a a' ?als h'' obs' h'`
  moreover {
    fix ad al v b
    assume "?vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
    hence "\<exists>T. P,h'' \<turnstile>jmm' ad@al : T \<and> P,h'' \<turnstile>jmm' v :\<le> T"
      using type_a' hext len
      by(fastsimp dest: vs intro: jmm'.addr_loc_type.intros elim: jmm'.addr_loc_type_hext_mono jmm'.conf_hext elim: notE split: split_if_asm) }
  moreover { fix ad al T
    assume adal: "P,h'' \<turnstile>jmm' ad@al : T"
    have "(ad, al) \<in> dom ?vs"
    proof(cases "\<exists>T. P,h \<turnstile>jmm' ad@al : T")
      case True
      with dom_vs[THEN subsetD, of "(ad, al)"]
      have "(ad, al) \<in> dom vs" by auto
      also note mrw_value_dom_mono
      finally show ?thesis .
    next
      case False
      have "ad = a'" using False adal dom_typeof[THEN equalityD1, THEN subsetD, of ad] hext len
        by(fastsimp elim: jmm'.addr_loc_type.cases dest: jmm'.typeof_addr_hext_mono jmm'.hext_arrD(2)[OF hext] intro: jmm'.addr_loc_type.intros)+
      with adal type_a' len show ?thesis by cases fastsimp+
    qed }
  hence "{(ad, al). \<exists>T. P,h'' \<turnstile>jmm' ad@al : T} \<subseteq> dom ?vs" by blast
  moreover from hext `jmm_typeof_addr h a = \<lfloor>Array T\<rfloor>`
  have type'a: "jmm_typeof_addr h'' a = \<lfloor>Array T\<rfloor>"
    and [simp]: "jmm_array_length h'' a = jmm_array_length h a"
    by(auto intro: jmm'.hext_arrD)
  from type'a have "list_all2 (\<lambda>al T. P,h'' \<turnstile>jmm' a@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI jmm'.addr_loc_type.intros)
  moreover from type_a' len have "list_all2 (\<lambda>al T. P,h'' \<turnstile>jmm' a'@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI jmm'.addr_loc_type.intros)
  moreover from `jmm_typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` hconf have "is_type P T"
    by(auto dest: jmm'.typeof_addr_is_type)
  with `jmm_new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` hconf have "P \<turnstile>jmm' h'' \<surd>"
    by(rule jmm'.hconf_new_arr_mono)
  ultimately 
  have "\<exists>obs'' h'''. jmm'_heap_copies P a a' ?als h'' obs'' h''' \<and>
                     ta_seq_consist P ?vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by(rule heap_copies_cut_and_update)
  then obtain obs'' h''' where copies: "jmm'_heap_copies P a a' ?als h'' obs'' h'''"
    and sc: "ta_seq_consist P ?vs (llist_of (map NormalAction obs''))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by blast
  from `jmm_typeof_addr h a = \<lfloor>Array T\<rfloor>` `n = jmm_array_length h a` `jmm_new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` copies
  have "jmm'_heap_clone P h a h''' \<lfloor>(NewArr a' T n # obs'', a')\<rfloor>"
    by(rule jmm'.heap_clone.ArrClone)
  moreover from sc have "ta_seq_consist P vs (llist_of (map NormalAction (NewArr a' T n # obs'')))" by simp
  moreover from eq have "eq_upto_seq_inconsist P (map NormalAction (NewArr a' T n # obs')) (map NormalAction (NewArr a' T n # obs'')) vs" by simp
  ultimately show ?thesis unfolding `obs = NewArr a' T n # obs'` by blast
qed

context final_thread begin

lemma red_external_cut_and_update:
  assumes wf: "wf_prog wf_md P"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile>jmm' ad@al : T \<and> P,shr s \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,shr s \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and red: "P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs'),shr s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>"
  and aok: "actions_ok s t ta"
  and hconf: "P \<turnstile>jmm' (shr s) \<surd>"
  shows "\<exists>ta'' va'' h''. P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs'), shr s\<rangle> -ta''\<rightarrow>ext \<langle>va'', h''\<rangle> \<and> 
                         actions_ok s t ta'' \<and>
                         ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)) \<and>
                         eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) vs"
using red aok
proof(cases)
  case (RedWaitInterrupt C)
  from wf `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P \<turnstile> C has interrupted_flag:Boolean (\<lparr>volatile = True\<rparr>) in Thread"
    by(rule wf_sub_Thread_has_interrupted_flag)
  with `jmm_typeof_addr (shr s) t = \<lfloor>Class C\<rfloor>`
  have adal: "P,shr s \<turnstile>jmm' t@interrupted_flag_loc : Boolean" ..
  hence "(t, interrupted_flag_loc) \<in> dom vs" using dom_vs by blast
  then obtain v b where vb: "vs (t, interrupted_flag_loc) = \<lfloor>(v, b)\<rfloor>" by auto
  from vs[OF this] adal have "P,shr s \<turnstile>jmm' v :\<le> Boolean" by(auto dest: jmm'.addr_loc_type_fun)
  then obtain b' where v: "v = Bool b'" by(auto simp add: jmm'.conf_def)
  from adal have "jmm_heap_read' P (shr s) t interrupted_flag_loc (Bool b')"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  thus ?thesis using vb v RedWaitInterrupt aok 
    by(cases b')(fastsimp intro: jmm'.RedWaitInterrupt jmm'.RedWait simp add: lock_ok_las_def finfun_upd_apply wset_actions_ok_def split: split_if_asm)+
next
  case (RedWait C)
  from wf `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P \<turnstile> C has interrupted_flag:Boolean (\<lparr>volatile = True\<rparr>) in Thread"
    by(rule wf_sub_Thread_has_interrupted_flag)
  with `jmm_typeof_addr (shr s) t = \<lfloor>Class C\<rfloor>`
  have adal: "P,shr s \<turnstile>jmm' t@interrupted_flag_loc : Boolean" ..
  hence "(t, interrupted_flag_loc) \<in> dom vs" using dom_vs by blast
  then obtain v b where vb: "vs (t, interrupted_flag_loc) = \<lfloor>(v, b)\<rfloor>" by auto
  from vs[OF this] adal have "P,shr s \<turnstile>jmm' v :\<le> Boolean" by(auto dest: jmm'.addr_loc_type_fun)
  then obtain b' where v: "v = Bool b'" by(auto simp add: jmm'.conf_def)
  from adal have "jmm_heap_read' P (shr s) t interrupted_flag_loc (Bool b')"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  thus ?thesis using vb v RedWait aok jmm'.heap_write_total[OF adal, of "Bool False"]
    by(cases b')(fastsimp intro: jmm'.RedWaitInterrupt jmm'.RedWait simp add: lock_ok_las_def finfun_upd_apply wset_actions_ok_def split: split_if_asm)+
next
  case (RedWaitInterrupted C b')
  from wf `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P \<turnstile> C has interrupted_flag:Boolean (\<lparr>volatile = True\<rparr>) in Thread"
    by(rule wf_sub_Thread_has_interrupted_flag)
  with `jmm_typeof_addr (shr s) t = \<lfloor>Class C\<rfloor>`
  have adal: "P,shr s \<turnstile>jmm' t@interrupted_flag_loc : Boolean" ..
  hence "(t, interrupted_flag_loc) \<in> dom vs" using dom_vs by blast
  then obtain v b where vb: "vs (t, interrupted_flag_loc) = \<lfloor>(v, b)\<rfloor>" by auto
  from vs[OF this] adal have "P,shr s \<turnstile>jmm' v :\<le> Boolean" by(auto dest: jmm'.addr_loc_type_fun)
  then obtain b'' where v: "v = Bool b''" by(auto simp add: jmm'.conf_def)
  from adal have "jmm_heap_read' P (shr s) t interrupted_flag_loc (Bool b'')"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  thus ?thesis using vb v RedWaitInterrupted aok by(fastsimp intro: jmm'.RedWaitInterrupted)
next
  case (RedClone obs a')
  with heap_clone_cut_and_update[OF wf vs dom_vs `jmm'_heap_clone P (shr s) a h' \<lfloor>(obs, a')\<rfloor>` hconf, of "\<lambda>_ _ _ b. b"]
  show ?thesis using aok
    by(fastsimp intro: jmm'.red_external.RedClone)
qed(fastsimp intro: jmm'.red_external.intros)+

end

declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

section {* Sequentially consistent completion from cut and update *}

locale Jinja_executions_aux =
  if_\<tau>multithreaded final r "convert_RA" \<tau>move +
  jmm!: executions_aux "lappend (llist_of start_heap_obs) ` if.\<E> start_state" P
  for final :: "'x \<Rightarrow> bool"
  and r :: "(addr, thread_id, 'x, 'm, 'w, obs_event) semantics"
  and \<tau>move :: "(addr, thread_id, 'x, 'm, 'w, obs_event) \<tau>moves" 
  and start_heap_obs :: "(thread_id \<times> obs_event action) list"
  and start_state :: "(addr, thread_id, status \<times> 'x, 'm, 'w) state"
  and P :: "'md prog" +
  assumes start_heap_obs_not_Read: "\<And>t ad al v. (t, NormalAction (ReadMem ad al v)) \<notin> set start_heap_obs"

sublocale Jinja_executions_aux < jmm_\<tau>multithreaded 
  init_fin_final
  init_fin
  "map NormalAction \<circ> convert_RA"
  init_fin_\<tau>move 
  P
.

context Jinja_executions_aux begin

lemma executions:
  assumes cut_and_update: "cut_and_update start_state (mrw_values P empty (map snd start_heap_obs))"
  shows "executions (lappend (llist_of start_heap_obs) ` if.\<E> start_state) P"
  (is "executions ?\<E> _")
proof -
  let ?n = "length start_heap_obs"

  show ?thesis
  proof
    fix E ws r
    assume E: "E \<in> ?\<E>"
      and wf: "P \<turnstile> (E, ws) \<surd>"
      and mrw: "\<And>a. \<lbrakk> a < r; a \<in> read_actions E \<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"
    show "\<exists>E'\<in>?\<E>. \<exists>ws'. P \<turnstile> (E', ws') \<surd> \<and> ltake (Fin r) E = ltake (Fin r) E' \<and>
                           sequentially_consistent P (E', ws') \<and>
                           action_tid E r = action_tid E' r \<and> action_obs E r \<approx> action_obs E' r \<and>
                           (r \<in> actions E \<longrightarrow> r \<in> actions E')"
    proof(cases "\<exists>r'. r' \<in> read_actions E \<and> r \<le> r'")
      case False
      have "sequentially_consistent P (E, ws)"
      proof(rule sequentially_consistentI)
        fix a
        assume "a \<in> read_actions E"
        with False have "a < r" by auto
        thus "P,E \<turnstile> a \<leadsto>mrw ws a" using `a \<in> read_actions E` by(rule mrw)
      qed
      moreover have "action_obs E r \<approx> action_obs E r" by(rule sim_action_refl)
      ultimately show ?thesis using wf E by blast
    next
      case True
      let ?P = "\<lambda>r'. r' \<in> read_actions E \<and> r \<le> r'"
      let ?r = "Least ?P"
      from True obtain r' where r': "?P r'" by blast
      hence r: "?P ?r" by(rule LeastI)
      {
        fix a
        assume "a < ?r" "a \<in> read_actions E"
        have "P,E \<turnstile> a \<leadsto>mrw ws a"
        proof(cases "a < r")
          case True
          thus ?thesis using `a \<in> read_actions E` by(rule mrw)
        next
          case False
          with `a \<in> read_actions E` have "?P a" by simp
          hence "?r \<le> a" by(rule Least_le)
          with `a < ?r` have False by simp
          thus ?thesis ..
        qed }
      note mrw' = this

      from E obtain E' E'' where E: "E = lappend (llist_of start_heap_obs) E''"
        and E'': "E'' \<in> if.\<E> start_state"  by auto

      from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
        and Runs: "if.mthr.Runs start_state E'"
        by(rule if.\<E>.cases)

      have r_len: "length start_heap_obs \<le> ?r"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?r < length start_heap_obs" by simp
        moreover with r E obtain t ad al v where "start_heap_obs ! ?r = (t, NormalAction (ReadMem ad al v))"
          by(cases "start_heap_obs ! ?r")(fastsimp elim!: read_actions.cases simp add: actions_def action_obs_def lnth_lappend1)
        ultimately have "(t, NormalAction (ReadMem ad al v)) \<in> set start_heap_obs" unfolding in_set_conv_nth by blast
        thus False by(simp add: start_heap_obs_not_Read)
      qed
      let ?n = "length start_heap_obs"
      from r r_len E have r: "?r - ?n \<in> read_actions E''"
        by(fastsimp elim!: read_actions.cases simp add: actions_lappend action_obs_def lnth_lappend2 elim: actionsE intro: read_actions.intros)
      
      from r have "?r - ?n \<in> actions E''" by(auto)
      hence "Fin (?r - ?n) < llength E''" by(rule actionsE)
      with Runs obtain r_m r_n t_r ta_r 
        where E_r: "lnth E'' (?r - ?n) = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)"
        and r_n: "r_n < length \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" and r_m: "Fin r_m < tlength E'"
        and r_conv: "?r - ?n = (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + r_n"
        and E'_r_m: "tnth E' r_m = (t_r, ta_r)"
        unfolding E' by(rule if.actions_\<E>E_aux)

      let ?E' = "tdropn (Suc r_m) E'"
      let ?r_m_E' = "ltake (Fin r_m) (llist_of_tllist E')"
      have E'_unfold: "E' = lappendt (ltake (Fin r_m) (llist_of_tllist E')) (TCons (tnth E' r_m) ?E')"
        unfolding tdropn_Suc_conv_tdropn[OF r_m] lappendt_ltake_tdropn ..
      hence "if.mthr.Runs start_state (lappendt ?r_m_E' (TCons (tnth E' r_m) ?E'))"
        using Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "if.mthr.\<tau>rtrancl3p start_state (list_of ?r_m_E') \<sigma>'"
        and Runs': "if.mthr.Runs \<sigma>' (TCons (tnth E' r_m) ?E')"
        by(rule if.mthr.Runs_lappendtE) simp
      from Runs' obtain \<sigma>'' \<sigma>''' where \<sigma>'_\<sigma>'': "if.mthr.silent_moves \<sigma>' \<sigma>''"
        and red_ra: "if.redT \<sigma>'' (t_r, ta_r) \<sigma>'''"
        and n\<tau>: "\<not> if.m\<tau>move \<sigma>'' (t_r, ta_r) \<sigma>'''"
        and Runs'': "if.mthr.Runs \<sigma>''' ?E'"
        unfolding E'_r_m by cases

      note \<sigma>_\<sigma>'
      also note if.mthr.silent_moves_into_\<tau>rtrancl3p[OF \<sigma>'_\<sigma>'']
      finally have \<sigma>_\<sigma>'': "if.mthr.\<tau>rtrancl3p start_state (list_of ?r_m_E') \<sigma>''" by simp

      let ?vs = "mrw_values P empty (map snd start_heap_obs)"
      { fix a
        assume "a < ?r"
          and "a \<in> read_actions E"
        have "a < r"
        proof(rule ccontr)
          assume "\<not> a < r"
          with `a \<in> read_actions E` have "?P a" by simp
          hence "?r \<le> a" by(rule Least_le)
          with `a < ?r` show False by simp
        qed
        hence "P,E \<turnstile> a \<leadsto>mrw ws a" using `a \<in> read_actions E` by(rule mrw) }
      with `E \<in> ?\<E>` wf have "ta_seq_consist P empty (lmap snd (ltake (Fin ?r) E))"
        by(rule jmm.ta_seq_consist_mrwI)

      hence start_sc: "ta_seq_consist P empty (llist_of (map snd start_heap_obs))"
        and "ta_seq_consist P ?vs (lmap snd (ltake (Fin (?r - ?n)) E''))"
        using `?n \<le> ?r` unfolding E ltake_lappend lmap_lappend_distrib
        by(simp_all add: ta_seq_consist_lappend o_def)

      note this(2) also from r_m
      have r_m_sum_len_eq: "(\<Sum>i<r_m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) = Fin (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(subst setsum_hom[symmetric, where f=Fin])(auto simp add: zero_inat_def split_def less_trans[where y="Fin r_m"] intro: setsum_cong)
      hence "ltake (Fin (?r - ?n)) E'' = 
            lappend (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E')) 
                    (ltake (Fin r_n) (ldrop (Fin (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) E''))"
        unfolding ltake_lmap[symmetric] lconcat_ltake r_conv plus_inat_simps(1)[symmetric] ltake_plus_conv_lappend
        unfolding E' by simp
      finally have "ta_seq_consist P ?vs (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E')))"
        and sc_ta_r: "ta_seq_consist P (mrw_values P ?vs (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))))) (lmap snd (ltake (Fin r_n) (ldropn (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) E'')))"
        unfolding lmap_lappend_distrib by(simp_all add: ta_seq_consist_lappend split_def)
      note this(1) also
      have "lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ltake (Fin r_m) (llist_of_tllist E'))))
            = llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E')))"
        unfolding lmap_lconcat lmap_compose[symmetric] o_def split_def lconcat_llist_of[symmetric] map_map lmap_llist_of[symmetric]
        by simp
      finally have "ta_seq_consist P ?vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E'))))" .
      from sequential_completion[OF cut_and_update ta_seq_consist_convert_RA \<sigma>_\<sigma>'' this red_ra n\<tau>]
      obtain ta' ttas' 
        where "if.mthr.Runs \<sigma>'' (TCons (t_r, ta') ttas')"
        and sc: "ta_seq_consist P (mrw_values P empty (map snd start_heap_obs)) 
                   (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of (list_of ?r_m_E')) (LCons (t_r, ta') (llist_of_tllist ttas')))))"
          and eq_ta: "eq_upto_seq_inconsist P \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P ?vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E'))))"
          by blast

      let ?E_sc' = "lappendt (llist_of (list_of ?r_m_E')) (TCons (t_r, ta') ttas')"
      let ?E_sc'' = "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist ?E_sc'))"
      let ?E_sc = "lappend (llist_of start_heap_obs) ?E_sc''"

      from \<sigma>_\<sigma>'' `if.mthr.Runs \<sigma>'' (TCons (t_r, ta') ttas')`
      have "if.mthr.Runs start_state ?E_sc'" 
        by(rule if.mthr.\<tau>rtrancl3p_into_Runs)
      hence "?E_sc'' \<in> if.\<E> start_state" by(rule if.\<E>.intros)
      hence "?E_sc \<in> ?\<E>" by(rule imageI)
      moreover from sc have "ta_seq_consist P empty (lmap snd ?E_sc)"
        by(simp add: lmap_lappend_distrib o_def lmap_lconcat lmap_compose[symmetric] split_def ta_seq_consist_lappend start_sc del: lmap_compose)
      from jmm.ta_seq_consist_imp_sequentially_consistent[OF `?E_sc \<in> ?\<E>` this]
      obtain ws_sc where "sequentially_consistent P (?E_sc, ws_sc)"
        and "P \<turnstile> (?E_sc, ws_sc) \<surd>" by blast
      moreover {
        have Fin_sum_r_m_eq: "Fin (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))"
          by(auto intro: setsum_cong simp add: less_trans[OF _ r_m] lnth_ltake llength_lconcat_lfinite_conv_sum setsum_hom[symmetric, where f=Fin] zero_inat_def[symmetric] split_beta)
        also have "\<dots> \<le> llength E''" unfolding E'
          by(blast intro: lprefix_llength_le lprefix_lconcatI lmap_lprefix)
        finally have r_m_E: "ltake (Fin (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>))) E = ltake (Fin (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>))) ?E_sc"
          by(simp add: ltake_lappend lappend_eq_lappend_conv lmap_lappend_distrib r_m_sum_len_eq ltake_lmap[symmetric] min_def zero_inat_def[symmetric] E E' lconcat_ltake ltake_all del: ltake_lmap)

        have drop_r_m_E: "ldropn (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) E = lappend (llist_of (map (Pair t_r) \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ldropn (Suc r_m) (llist_of_tllist E'))))"
          (is "_ = ?drop_r_m_E") using E'_r_m unfolding E E'
          by(subst (2) E'_unfold)(simp add: ldropn_lappend2 lmap_lappend_distrib Fin_sum_r_m_eq[symmetric])

        have drop_r_m_E_sc: "ldropn (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) ?E_sc =
          lappend (llist_of (map (Pair t_r) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist ttas')))"
          by(simp add: ldropn_lappend2 lmap_lappend_distrib Fin_sum_r_m_eq[symmetric])

        let ?vs_r_m = "mrw_values P ?vs (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))))"
        note sc_ta_r also
        from drop_r_m_E have "ldropn (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) E'' = ?drop_r_m_E"
          unfolding E by(simp add: ldropn_lappend2)
        also have "lmap snd (ltake (Fin r_n) \<dots>) = llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)" using r_n
          by(simp add: ltake_lappend lmap_lappend_distrib ltake_lmap[symmetric] take_map o_def zero_inat_def[symmetric] del: ltake_lmap)
        finally have sc_ta_r: "ta_seq_consist P ?vs_r_m (llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))" .
        note eq_ta
        also have "\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> @ drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" by simp
        finally have "eq_upto_seq_inconsist P (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> @ drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs_r_m"
          by(simp add: list_of_lconcat split_def o_def map_concat)
        from eq_upto_seq_inconsist_appendD[OF this sc_ta_r]
        have r_n': "r_n \<le> length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
          and take_r_n_eq: "take r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>"
          and eq_r_n: "eq_upto_seq_inconsist P (drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>) (drop r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (mrw_values P ?vs_r_m (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))"
          using r_n by(simp_all add: min_def)
        from r_conv `?n \<le> ?r` have r_conv': "?r = (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) + r_n" by simp
        from r_n' r_n take_r_n_eq r_m_E drop_r_m_E drop_r_m_E_sc
        have take_r'_eq: "ltake (Fin ?r) E = ltake (Fin ?r) ?E_sc" unfolding r_conv'
          apply(subst (1 2) plus_inat_simps(1)[symmetric])
          apply(subst (1 2) ltake_plus_conv_lappend)
          apply(simp add: lappend_eq_lappend_conv ltake_lappend1 take_map)
          done
        hence take_r_eq: "ltake (Fin r) E = ltake (Fin r) ?E_sc"
          by(rule ltake_eq_ltake_antimono)(simp add: `?P ?r`)
        
        from eq_r_n nth_drop'[OF r_n, symmetric]
        have "drop r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<noteq> []" by(auto simp add: eq_upto_seq_inconsist_simps)
        hence r_n': "r_n < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" by simp
        hence eq_r_n: "\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n \<approx> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! r_n"
          using eq_r_n nth_drop'[OF r_n, symmetric] nth_drop'[OF r_n', symmetric]
          by(simp add: eq_upto_seq_inconsist_simps split: action.split_asm obs_event.split_asm split_if_asm)
        obtain tid_eq: "action_tid E r = action_tid ?E_sc r" 
          and obs_eq: "action_obs E r \<approx> action_obs ?E_sc r"
        proof(cases "r < ?r")
          case True
          { from True have "action_tid E r = action_tid (ltake (Fin ?r) E) r"
              by(simp add: action_tid_def lnth_ltake)
            also note take_r'_eq
            also have "action_tid (ltake (Fin ?r) ?E_sc) r = action_tid ?E_sc r"
              using True by(simp add: action_tid_def lnth_ltake)
            finally have "action_tid E r = action_tid ?E_sc r" . }
          moreover
          { from True have "action_obs E r = action_obs (ltake (Fin ?r) E) r"
              by(simp add: action_obs_def lnth_ltake)
            also note take_r'_eq
            also have "action_obs (ltake (Fin ?r) ?E_sc) r = action_obs ?E_sc r"
              using True by(simp add: action_obs_def lnth_ltake)
            finally have "action_obs E r \<approx> action_obs ?E_sc r" by simp }
          ultimately show thesis by(rule that)
        next
          case False
          with `?P ?r` have r_eq: "r = ?r" by simp
          hence "lnth E r = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)" using E_r r_conv' E by(simp add: lnth_lappend2)
          moreover have "lnth ?E_sc r = (t_r, \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! r_n)" using `?n \<le> ?r` r_n'
            by(subst r_eq)(simp add: r_conv lnth_lappend2 lmap_lappend_distrib Fin_sum_r_m_eq[symmetric] lnth_lappend1)
          ultimately have "action_tid E r = action_tid ?E_sc r" "action_obs E r \<approx> action_obs ?E_sc r"
            using eq_r_n by(simp_all add: action_tid_def action_obs_def)
          thus thesis by(rule that)
        qed
        
        have "Fin r < Fin ?n + llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend ?r_m_E' (LCons (t_r, ta') LNil))))"
          using `?P ?r` r_n' unfolding lmap_lappend_distrib
          by(simp add: lconcat_lappend Fin_sum_r_m_eq[symmetric] r_conv')
        also have "llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend ?r_m_E' (LCons (t_r, ta') LNil)))) \<le> llength ?E_sc''"
          by(rule lprefix_llength_le[OF lprefix_lconcatI])(simp add: lmap_lprefix)
        finally have "r \<in> actions ?E_sc" by(simp add: actions_def add_left_mono)
        note this tid_eq obs_eq take_r_eq }
      ultimately show ?thesis by blast
    qed
  qed
qed

end

end
