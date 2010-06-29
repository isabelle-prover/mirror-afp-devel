(*  Title:      JinjaThreads/Common/ExternalCallWF.thy
    Author:     Andreas Lochbihler
*)

header{* \isaheader{ Properties of external calls in well-formed programs } *}

theory ExternalCallWF imports WellForm "../Framework/FWSemantics" begin

lemma list_all2_refl_conv: -- "Move to Aux"
  "list_all2 P xs xs \<longleftrightarrow> (\<forall>x\<in>set xs. P x x)"
unfolding list_all2_conv_all_nth Ball_def in_set_conv_nth
by auto

lemma WT_external_is_type:
  assumes "wf_prog wf_md P" "P \<turnstile> T\<bullet>M(TS) :: U" "is_type P T"
  shows "is_type P U" "set TS \<subseteq> is_type P"
using assms
apply(auto elim!: external_WT_defs.cases external_WT.cases)
apply(simp add: mem_def)
done

context heap_base begin

lemma WT_red_external_aggr_imp_red_external:
  "\<lbrakk> wf_prog wf_md P; (ta, va, h') \<in> red_external_aggr P t a M vs h; P,h \<turnstile> a\<bullet>M(vs) : U; P,h \<turnstile> t \<surd>t \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
apply(auto elim!: external_WT.cases external_WT_defs_cases external_WT'.cases simp add: red_external_aggr_def widen_Class split_beta intro: red_external.intros[simplified] split: split_if_asm dest!: tconfD)
apply(fastsimp simp add: list_all2_Cons2 intro: red_external.intros[simplified])
apply(fastsimp simp add: list_all2_Cons2 intro: red_external.intros[simplified])
apply(fastsimp elim: external_WT_defs.cases simp add: widen_Class)+
done

lemma WT_red_external_list_conv:
  "\<lbrakk> wf_prog wf_md P; P,h \<turnstile> a\<bullet>M(vs) : U; P,h \<turnstile> t \<surd>t \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<longleftrightarrow> (ta, va, h') \<in> red_external_aggr P t a M vs h"
by(blast intro: WT_red_external_aggr_imp_red_external red_external_imp_red_external_aggr)

lemma red_external_new_thread_sees:
  "\<lbrakk> wf_prog wf_md P; P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = \<lfloor>Class C\<rfloor> \<and> (\<exists>T meth D. P \<turnstile> C sees M':[]\<rightarrow>T = meth in D)"
by(fastsimp elim!: red_external.cases simp add: widen_Class ta_upd_simps dest: sub_Thread_sees_run)

end

subsection {* Progress theorems for external calls *}

context heap_progress begin

lemma red_external_Suspend_Notified_Interrupted:
  assumes wf: "wf_prog wf_md P"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and suspend: "Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "h' \<unlhd> h''"
  shows "\<exists>ta' va'. P,t \<turnstile> \<langle>a\<bullet>M(vs), h''\<rangle> -ta'\<rightarrow>ext \<langle>va', h''\<rangle> \<and> Notified \<in> set \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> \<and> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = {}" (is ?thesis1)
  and "\<exists>ta' va' h'''. P,t \<turnstile> \<langle>a\<bullet>M(vs), h''\<rangle> -ta'\<rightarrow>ext \<langle>va', h'''\<rangle> \<and> Interrupted \<in> set \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> \<and> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = {}" (is ?thesis2)
proof -
  from red suspend RedWaitNotified show ?thesis1
    by cases(fastsimp simp del: split_paired_Ex simp add: collect_locks_def)+
next
  from assms obtain C where [simp]: "h' = h" "M = wait" "vs = []"
    and "typeof_addr h t = \<lfloor>Class C\<rfloor>" "P \<turnstile> C \<preceq>\<^sup>* Thread"
    by(auto elim: red_external.cases simp add: ta_upd_simps)
  with `h' \<unlhd> h''` have "typeof_addr h'' t = \<lfloor>Class C\<rfloor>"
    by(auto intro: typeof_addr_hext_mono)
  from wf `P \<turnstile> C \<preceq>\<^sup>* Thread` have "P \<turnstile> C has interrupted_flag:Boolean in Thread"
    by(rule wf_sub_Thread_has_interrupted_flag)
  with `typeof_addr h'' t = \<lfloor>Class C\<rfloor>`
  have "P,h'' \<turnstile> t@interrupted_flag_loc : Boolean" ..
  from heap_write_total[OF this, of "Bool False"]
  obtain h''' where "heap_write h'' t interrupted_flag_loc (Bool False) h'''" ..
  with `typeof_addr h'' t = \<lfloor>Class C\<rfloor>` `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> -\<epsilon>\<lbrace>\<^bsub>w\<^esub> Interrupted \<rbrace>
                                \<lbrace>\<^bsub>o\<^esub>  WriteMem t interrupted_flag_loc (Bool False)\<rbrace>\<rightarrow>ext
              \<langle>RetEXC InterruptedException, h'''\<rangle>"
    by(rule RedWaitInterrupted)
  thus ?thesis2 by(fastsimp simp del: split_paired_Ex simp add: collect_locks_def)
qed

lemma heap_copy_loc_progress:
  assumes hconf: "hconf h"
  and alconfa: "P,h \<turnstile> a@al : T"
  and alconfa': "P,h \<turnstile> a'@al : T"
  shows "\<exists>v h'. heap_copy_loc a a' al h ([ReadMem a al v, WriteMem a' al v]) h' \<and> P,h \<turnstile> v :\<le> T \<and> hconf h'"
proof -
  from heap_read_total[OF hconf alconfa]
  obtain v where "heap_read h a al v" "P,h \<turnstile> v :\<le> T" by blast
  moreover from heap_write_total[OF alconfa', of v] obtain h' where "heap_write h a' al v h'" ..
  moreover hence "hconf h'" using hconf alconfa' `P,h \<turnstile> v :\<le> T` by(rule hconf_heap_write_mono)
  ultimately show ?thesis by(blast intro: heap_copy_loc.intros)
qed

lemma heap_copies_progress:
  assumes "hconf h"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts"
  shows "\<exists>vs h'. heap_copies a a' als h (concat (map (\<lambda>(al, v). [ReadMem a al v, WriteMem a' al v]) (zip als vs))) h' \<and> hconf h'"
using assms
proof(induct als arbitrary: h Ts)
  case Nil thus ?case by(auto intro: heap_copies.Nil)
next
  case (Cons al als)
  from `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) (al # als) Ts`
  obtain T Ts' where [simp]: "Ts = T # Ts'"
    and "P,h \<turnstile> a@al : T" "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from `list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) (al # als) Ts`
  have "P,h \<turnstile> a'@al : T" and "list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts'" by simp_all
  from `hconf h` `P,h \<turnstile> a@al : T` `P,h \<turnstile> a'@al : T`
  obtain v h' where "heap_copy_loc a a' al h [ReadMem a al v, WriteMem a' al v] h'"
    and "hconf h'" by(auto dest: heap_copy_loc_progress)
  moreover {
    hence "h \<unlhd> h'" by-(rule hext_heap_copy_loc)
    note `hconf h'`
    moreover from `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'`
    have "list_all2 (\<lambda>al T. P,h' \<turnstile> a@al : T) als Ts'"
      by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h'`])
    moreover from `list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts'`
    have "list_all2 (\<lambda>al T. P,h' \<turnstile> a'@al : T) als Ts'"
      by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h'`])
    ultimately have "\<exists>vs h''. heap_copies a a' als h' (concat (map (\<lambda>(al, v). [ReadMem a al v, WriteMem a' al v]) (zip als vs))) h'' \<and> hconf h''"
      by(rule Cons) }
  then obtain vs h''
    where "heap_copies a a' als h' (concat (map (\<lambda>(al, v). [ReadMem a al v, WriteMem a' al v]) (zip als vs))) h''"
    and "hconf h''" by blast
  ultimately have "heap_copies a a' (al # als) h ([ReadMem a al v, WriteMem a' al v] @ (concat (map (\<lambda>(al, v). [ReadMem a al v, WriteMem a' al v]) (zip als vs)))) h''"
    by- (rule heap_copies.Cons)
  also have "[ReadMem a al v, WriteMem a' al v] @ (concat (map (\<lambda>(al, v). [ReadMem a al v, WriteMem a' al v]) (zip als vs))) =
            (concat (map (\<lambda>(al, v). [ReadMem a al v, WriteMem a' al v]) (zip (al # als) (v # vs))))" by simp
  finally show ?case using `hconf h''` by blast
qed

lemma heap_clone_progress:
  assumes wf: "wf_prog wf_md P"
  and typea: "typeof_addr h a = \<lfloor>T\<rfloor>"
  and hconf: "hconf h"
  shows "\<exists>h' res. heap_clone P h a h' res \<and> hconf h'"
proof -
  from typea hconf have "is_type P T" by(rule typeof_addr_is_type)
  from typea have "(\<exists>C. T = Class C) \<or> (\<exists>U. T = Array U)"
    by(rule typeof_addr_eq_Some_conv)
  thus ?thesis
  proof
    assume "\<exists>C. T = Class C"
    then obtain C where [simp]: "T = Class C" ..
    obtain h' res where new: "new_obj h C = (h', res)" by(cases "new_obj h C")
    hence "h \<unlhd> h'" by(rule hext_new_obj)
    from `is_type P T` new have "hconf h'"
      using hconf by simp (rule hconf_new_obj_mono) 
    show ?thesis
    proof(cases res)
      case None
      with typea new ObjFail[of h a C h' P]
      show ?thesis using `hconf h'` by auto
    next
      case (Some a')
      from `is_type P T` have "is_class P C" by simp
      from wf_Fields_Ex[OF wf this]
      obtain FDTs where FDTs: "P \<turnstile> C has_fields FDTs" ..
      let ?als = "map (\<lambda>((F, D), T). CField D F) FDTs"
      let ?Ts = "map snd FDTs"
      from wf FDTs have "distinct (map fst FDTs)" by(rule has_fields_distinct)
      with typea FDTs have "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) ?als ?Ts"
        unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
        by(fastsimp intro!: addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
      hence "list_all2 (\<lambda>al T. P,h' \<turnstile> a@al : T) ?als ?Ts"
        by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h'`])
      moreover from new Some
      have "typeof_addr h' a' = \<lfloor>Class C\<rfloor>" by(auto dest: new_obj_SomeD)
      with FDTs `distinct (map fst FDTs)`
      have "list_all2 (\<lambda>al T. P,h' \<turnstile> a'@al : T) ?als ?Ts"
        unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
        by(fastsimp intro!: addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
      ultimately obtain obs h'' where "heap_copies a a' ?als h' obs h''" "hconf h''"
        by(blast dest: heap_copies_progress[OF `hconf h'`])
      with typea new Some FDTs ObjClone[of h a C h' a' P FDTs obs h'']
      show ?thesis by auto
    qed
  next
    assume "\<exists>U. T = Array U"
    then obtain U where T [simp]: "T = Array U" ..
    obtain h' res where new: "new_arr h U (array_length h a) = (h', res)"
      by(cases "new_arr h U (array_length h a)")
    hence "h \<unlhd> h'" by(rule hext_new_arr)
    from new hconf `is_type P T` have "hconf h'" by simp(rule hconf_new_arr_mono)
    show ?thesis
    proof(cases res)
      case None
      with typea new ArrFail[of h a U h' P]
      show ?thesis using `hconf h'` by auto
    next
      case (Some a')
      let ?n = "array_length h a"
      let ?als = "map ACell [0..<?n]"
      let ?Ts = "replicate ?n U"
      from `h \<unlhd> h'` typea have type'a: "typeof_addr h' a = \<lfloor>Array U\<rfloor>"
        and [simp]: "array_length h' a = array_length h a" by(auto intro: hext_arrD)
      from type'a have "list_all2 (\<lambda>al T. P,h' \<turnstile> a@al : T) ?als ?Ts"
        by(fastsimp intro: list_all2_all_nthI addr_loc_type.intros)
      moreover from new Some
      have "typeof_addr h' a' = \<lfloor>Array U\<rfloor>" "array_length h' a' = array_length h a"
        by(auto dest: new_arr_SomeD)
      hence "list_all2 (\<lambda>al T. P,h' \<turnstile> a'@al : T) ?als ?Ts"
        by(fastsimp intro: list_all2_all_nthI addr_loc_type.intros)
      ultimately obtain obs h'' where "heap_copies a a' ?als h' obs h''" "hconf h''"
        by(blast dest: heap_copies_progress[OF `hconf h'`])
      with typea new Some ArrClone[of h a U "?n" h' a' obs h'' P]
      show ?thesis by auto
    qed
  qed
qed

theorem external_call_progress:
  assumes wf: "wf_prog wf_md P"
  and wt: "P,h \<turnstile> a\<bullet>M(vs) : U"
  and hconf: "hconf h"
  shows "\<exists>ta va h'. P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
proof -
  note [simp del] = split_paired_Ex
  from wt obtain T Ts Ts'
    where T: "typeof_addr h a = \<lfloor>T\<rfloor>" and Ts: "map typeof\<^bsub>h\<^esub> vs = map Some Ts"
    and "P \<turnstile> T\<bullet>M(Ts') :: U" and subTs: "P \<turnstile> Ts [\<le>] Ts'"
    unfolding external_WT'_iff by blast
  from `P \<turnstile> T\<bullet>M(Ts') :: U` obtain T' where "T'\<bullet>M(Ts') :: U"
    and subT': "P \<turnstile> T \<le> T'" and ext: "is_external_call P T M"
    by(rule external_WT.cases) clarsimp
  from `T'\<bullet>M(Ts') :: U` subT' ext T Ts subTs show ?thesis
  proof cases
    assume [simp]: "T' = Class Thread" "M = interrupt" "Ts' = []" "U = Void"
    from wf have "P \<turnstile> Thread has interrupted_flag:Boolean in Thread" by(rule wf_Thread_has_interrupted_flag)
    moreover from subT' typeof_addr_eq_Some_conv[OF T]
    obtain C where [simp]: "T = Class C" and "P \<turnstile> C \<preceq>\<^sup>* Thread" by(auto simp add: widen_Class)
    ultimately have "P \<turnstile> C has interrupted_flag:Boolean in Thread" by(blast intro: has_field_mono)
    with T have "P,h \<turnstile> a@interrupted_flag_loc : Boolean"
      by(auto intro: addr_loc_type.intros)
    then obtain h' where "heap_write h a interrupted_flag_loc (Bool True) h'"
      by(blast dest: heap_write_total)
    with subT' ext T Ts subTs `P \<turnstile> C \<preceq>\<^sup>* Thread` show ?thesis by(auto intro: red_external.intros)
  next
    assume [simp]: "T' = Class Object" "M = clone" "Ts' = []" "U = Class Object"
    from heap_clone_progress[OF wf T hconf] obtain h' res where "heap_clone P h a h' res" by blast
    thus ?thesis using subTs Ts by(cases res)(auto intro: red_external.intros)
  next
    assume [simp]: "T' = Class Object" "M = equals" "Ts' = [Class Object]" "U = Boolean"
    from subTs Ts obtain v where [simp]: "vs = [v]"
      by(auto simp add: map_eq_map_conv list_all2_Cons2)
    thus ?thesis by(fastsimp intro: red_external.intros)
  qed(fastsimp simp add: widen_Class is_external_call_def intro: red_external.intros)+
qed

end

subsection {* Lemmas for preservation of deadlocked threads *}

lemma (in heap_progress) red_external_Lock_hext:
  assumes wf: "wf_prog wf_md P"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and Lock: "Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)"
  and hext: "h \<unlhd> h''"
  and hconf: "hconf h''"
  shows "\<exists>va' ta' h'''. P,t \<turnstile> \<langle>a\<bullet>M(vs), h''\<rangle> -ta'\<rightarrow>ext \<langle>va', h'''\<rangle> \<and> 
                        collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>}"
using red Lock
proof cases
  case (RedWait C)
  from `h \<unlhd> h''` `typeof_addr h t = \<lfloor>Class C\<rfloor>`
  have type: "typeof_addr h'' t = \<lfloor>Class C\<rfloor>" by(rule typeof_addr_hext_mono)
  from wf have "P \<turnstile> Thread has interrupted_flag:Boolean in Thread"
    by(rule wf_Thread_has_interrupted_flag)
  hence "P \<turnstile> C has interrupted_flag:Boolean in Thread"
    using `P \<turnstile> C \<preceq>\<^sup>* Thread` by(rule has_field_mono)
  with type have "P,h'' \<turnstile> t@interrupted_flag_loc : Boolean"
    by(rule addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where read: "heap_read h'' t interrupted_flag_loc v"
    and "P,h'' \<turnstile> v :\<le> Boolean" by blast
  from `P,h'' \<turnstile> v :\<le> Boolean` obtain b
    where [simp]: "v = Bool b" by(auto simp add: conf_def)
  show ?thesis
  proof(cases b)
    case True
    let ?ta = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), 
                                    WriteMem t interrupted_flag_loc (Bool False)\<rbrace>"
    from heap_write_total[OF `P,h'' \<turnstile> t@interrupted_flag_loc : Boolean`, of "Bool False"]
    obtain h''' where "heap_write h'' t interrupted_flag_loc (Bool False) h'''" ..
    from read RedWaitInterrupt[OF type `P \<turnstile> C \<preceq>\<^sup>* Thread` _ this, of a] True
    have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> -?ta\<rightarrow>ext \<langle>RetEXC InterruptedException, h'''\<rangle>" by simp
    with RedWait show ?thesis
      by(auto simp add: collect_locks_def ta_upd_simps finfun_upd_apply intro!: exI split: split_if_asm)
  next
    case False
    from read red_external.RedWait[OF type `P \<turnstile> C \<preceq>\<^sup>* Thread`, of a] RedWait False
    have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> -ta\<rightarrow>ext \<langle>va, h''\<rangle>" by simp
    thus ?thesis using RedWait by fastsimp
  qed
next
  case (RedWaitInterrupt C)
  from `h \<unlhd> h''` `typeof_addr h t = \<lfloor>Class C\<rfloor>`
  have type: "typeof_addr h'' t = \<lfloor>Class C\<rfloor>" by(rule typeof_addr_hext_mono)
  from wf have "P \<turnstile> Thread has interrupted_flag:Boolean in Thread"
    by(rule wf_Thread_has_interrupted_flag)
  hence "P \<turnstile> C has interrupted_flag:Boolean in Thread"
    using `P \<turnstile> C \<preceq>\<^sup>* Thread` by(rule has_field_mono)
  with type have "P,h'' \<turnstile> t@interrupted_flag_loc : Boolean"
    by(rule addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where read: "heap_read h'' t interrupted_flag_loc v"
    and "P,h'' \<turnstile> v :\<le> Boolean" by blast
  from `P,h'' \<turnstile> v :\<le> Boolean` obtain b
    where [simp]: "v = Bool b" by(auto simp add: conf_def)
  show ?thesis
  proof(cases b)
    case True
    let ?ta = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), 
                                    WriteMem t interrupted_flag_loc (Bool False)\<rbrace>"
    from heap_write_total[OF `P,h'' \<turnstile> t@interrupted_flag_loc : Boolean`, of "Bool False"]
    obtain h''' where "heap_write h'' t interrupted_flag_loc (Bool False) h'''" ..
    from read red_external.RedWaitInterrupt[OF type `P \<turnstile> C \<preceq>\<^sup>* Thread` _ this, of a] True
    have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> -?ta\<rightarrow>ext \<langle>RetEXC InterruptedException, h'''\<rangle>" by simp
    with RedWaitInterrupt show ?thesis
      by(auto simp add: collect_locks_def ta_upd_simps finfun_upd_apply intro!: exI split: split_if_asm)
  next
    case False
    let ?ta = "\<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), SyncUnlock a\<rbrace>"
    from read red_external.RedWait[OF type `P \<turnstile> C \<preceq>\<^sup>* Thread`, of a] False
    have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> - ?ta\<rightarrow>ext \<langle>RetStaySame, h''\<rangle>" by simp
    thus ?thesis using RedWaitInterrupt 
      by(auto simp add: collect_locks_def ta_upd_simps finfun_upd_apply intro!: exI split: split_if_asm)
  qed
qed(fastsimp simp add: finfun_upd_apply split_beta ta_upd_simps intro: red_external.intros[simplified])+

lemma (in heap) red_external_Join_hext:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Join t' \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; h \<unlhd> h'' \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>M(vs), h''\<rangle> -ta\<rightarrow>ext \<langle>va, h''\<rangle>"
by(auto simp add: ta_upd_simps elim!: red_external.cases intro!: RedJoin[simplified] intro: typeof_addr_hext_mono)

lemma (in heap_progress) red_external_wt_hconf_hext:
  assumes wf: "wf_prog wf_md P"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>"
  and hext: "h'' \<unlhd> h"
  and wt: "P,h'' \<turnstile> a\<bullet>M(vs) : U"
  and tconf: "P,h'' \<turnstile> t \<surd>t"
  and hconf: "hconf h''" 
  shows "\<exists>ta' va' h'''. P,t \<turnstile> \<langle>a\<bullet>M(vs),h''\<rangle> -ta'\<rightarrow>ext \<langle>va', h'''\<rangle> \<and> 
                        collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>}"
using red wt hext
proof cases
  case (RedWait C)
  from tconf `typeof_addr h t = \<lfloor>Class C\<rfloor>` 
  have type: "typeof_addr h'' t = \<lfloor>Class C\<rfloor>"
    by(fastsimp dest: tconfD typeof_addr_hext_mono[OF hext])
  from wf have "P \<turnstile> Thread has interrupted_flag:Boolean in Thread"
    by(rule wf_Thread_has_interrupted_flag)
  hence "P \<turnstile> C has interrupted_flag:Boolean in Thread"
    using `P \<turnstile> C \<preceq>\<^sup>* Thread` by(rule has_field_mono)
  with type have "P,h'' \<turnstile> t@interrupted_flag_loc : Boolean"
    by(rule addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where read: "heap_read h'' t interrupted_flag_loc v"
    and "P,h'' \<turnstile> v :\<le> Boolean" by blast
  from `P,h'' \<turnstile> v :\<le> Boolean` obtain b
    where [simp]: "v = Bool b" by(auto simp add: conf_def)
  show ?thesis
  proof(cases b)
    case True
    let ?ta = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), 
                                    WriteMem t interrupted_flag_loc (Bool False)\<rbrace>"
    from heap_write_total[OF `P,h'' \<turnstile> t@interrupted_flag_loc : Boolean`, of "Bool False"]
    obtain h''' where "heap_write h'' t interrupted_flag_loc (Bool False) h'''" ..
    from read RedWaitInterrupt[OF type `P \<turnstile> C \<preceq>\<^sup>* Thread` _ this, of a] True
    have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> -?ta\<rightarrow>ext \<langle>RetEXC InterruptedException, h'''\<rangle>" by simp
    with RedWait show ?thesis
      by(auto simp add: collect_locks_def ta_upd_simps finfun_upd_apply intro!: exI split: split_if_asm)
  next
    case False
    from read red_external.RedWait[OF type `P \<turnstile> C \<preceq>\<^sup>* Thread`, of a] RedWait False
    have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> -ta\<rightarrow>ext \<langle>va, h''\<rangle>" by simp
    thus ?thesis using RedWait by fastsimp
  qed
next
  case (RedWaitInterrupt C)
  from tconf `typeof_addr h t = \<lfloor>Class C\<rfloor>` 
  have type: "typeof_addr h'' t = \<lfloor>Class C\<rfloor>"
    by(fastsimp dest: tconfD typeof_addr_hext_mono[OF hext])
  from wf have "P \<turnstile> Thread has interrupted_flag:Boolean in Thread"
    by(rule wf_Thread_has_interrupted_flag)
  hence "P \<turnstile> C has interrupted_flag:Boolean in Thread"
    using `P \<turnstile> C \<preceq>\<^sup>* Thread` by(rule has_field_mono)
  with type have "P,h'' \<turnstile> t@interrupted_flag_loc : Boolean"
    by(rule addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where read: "heap_read h'' t interrupted_flag_loc v"
    and "P,h'' \<turnstile> v :\<le> Boolean" by blast
  from `P,h'' \<turnstile> v :\<le> Boolean` obtain b
    where [simp]: "v = Bool b" by(auto simp add: conf_def)
  show ?thesis
  proof(cases b)
    case True
    let ?ta = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), 
                                    WriteMem t interrupted_flag_loc (Bool False)\<rbrace>"
    from heap_write_total[OF `P,h'' \<turnstile> t@interrupted_flag_loc : Boolean`, of "Bool False"]
    obtain h''' where "heap_write h'' t interrupted_flag_loc (Bool False) h'''" ..
    from read red_external.RedWaitInterrupt[OF type `P \<turnstile> C \<preceq>\<^sup>* Thread` _ this, of a] True
    have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> -?ta\<rightarrow>ext \<langle>RetEXC InterruptedException, h'''\<rangle>" by simp
    with RedWaitInterrupt show ?thesis
      by(auto simp add: collect_locks_def finfun_upd_apply ta_upd_simps intro!: exI split: split_if_asm)
  next
    case False
    let ?ta = "\<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), SyncUnlock a\<rbrace>"
    from read red_external.RedWait[OF type `P \<turnstile> C \<preceq>\<^sup>* Thread`, of a] False
    have "P,t \<turnstile> \<langle>a\<bullet>wait([]), h''\<rangle> - ?ta\<rightarrow>ext \<langle>RetStaySame, h''\<rangle>" by simp
    thus ?thesis using RedWaitInterrupt 
      by(auto simp add: collect_locks_def finfun_upd_apply ta_upd_simps intro!: exI split: split_if_asm)
  qed
next
  case (RedInterrupt C)
  from `typeof_addr h a = \<lfloor>Class C\<rfloor>` wt `h'' \<unlhd> h`
  have type: "typeof_addr h'' a = \<lfloor>Class C\<rfloor>"
    by(auto elim!: external_WT'.cases dest: typeof_addr_hext_mono)
  from wf have "P \<turnstile> Thread has interrupted_flag:Boolean in Thread"
    by(rule wf_Thread_has_interrupted_flag)
  hence "P \<turnstile> C has interrupted_flag:Boolean in Thread"
    using `P \<turnstile> C \<preceq>\<^sup>* Thread` by(rule has_field_mono)
  with type have "P,h'' \<turnstile> a@interrupted_flag_loc : Boolean"
    by(rule addr_loc_type.intros)
  from heap_write_total[OF this, of "Bool True"] obtain h''' 
    where "heap_write h'' a interrupted_flag_loc (Bool True) h'''" ..
  with type RedInterrupt show ?thesis
    by(fastsimp intro: red_external.RedInterrupt)
next
  case (RedClone obs a')
  from wt obtain T Ts Ts'
    where T: "typeof_addr h'' a = \<lfloor>T\<rfloor>" and "P \<turnstile> T\<bullet>M(Ts') :: U"
    unfolding external_WT'_iff by blast
  from `P \<turnstile> T\<bullet>M(Ts') :: U` obtain T' where "T'\<bullet>M(Ts') :: U"
    and subT': "P \<turnstile> T \<le> T'" by(rule external_WT.cases) clarsimp
  from `M = clone` `T'\<bullet>M(Ts') :: U` have [simp]: "T' = Class Object"
    by(auto elim!: external_WT_defs.cases)
  from heap_clone_progress[OF wf T hconf]
  obtain h''' res where "heap_clone P h'' a h''' res" by blast
  thus ?thesis using RedClone
    by(cases res)(fastsimp intro: red_external.intros)+
next
  case RedCloneFail
  from wt obtain T Ts Ts'
    where T: "typeof_addr h'' a = \<lfloor>T\<rfloor>" and "P \<turnstile> T\<bullet>M(Ts') :: U"
    unfolding external_WT'_iff by blast
  from `P \<turnstile> T\<bullet>M(Ts') :: U` obtain T' where "T'\<bullet>M(Ts') :: U"
    and subT': "P \<turnstile> T \<le> T'" by(rule external_WT.cases) clarsimp
  from `M = clone` `T'\<bullet>M(Ts') :: U` have [simp]: "T' = Class Object"
    by(auto elim!: external_WT_defs.cases)
  from heap_clone_progress[OF wf T hconf]
  obtain h''' res where "heap_clone P h'' a h''' res" by blast
  thus ?thesis using RedCloneFail
    by(cases res)(fastsimp intro: red_external.intros)+
qed(fastsimp simp add: ta_upd_simps elim!: external_WT'.cases intro: red_external.intros[simplified] dest: typeof_addr_hext_mono)+

subsection {* Preservation of heap conformance *}

context heap_conf_read begin

lemma hconf_heap_copy_loc_mono:
  assumes "heap_copy_loc a a' al h obs h'"
  and "hconf h"
  and "P,h \<turnstile> a@al : T" "P,h \<turnstile> a'@al : T"
  shows "hconf h'"
proof -
  from `heap_copy_loc a a' al h obs h'` obtain v 
    where read: "heap_read h a al v" 
    and "write": "heap_write h a' al v h'" by cases auto
  from read `P,h \<turnstile> a@al : T` `hconf h` have "P,h \<turnstile> v :\<le> T"
    by(rule heap_read_conf)
  with "write" `hconf h` `P,h \<turnstile> a'@al : T` show ?thesis
    by(rule hconf_heap_write_mono)
qed

lemma hconf_heap_copies_mono:
  assumes "heap_copies a a' als h obs h'"
  and "hconf h"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts"
  shows "hconf h'"
using assms
proof(induct arbitrary: Ts)
  case Nil thus ?case by simp
next
  case (Cons al h ob h' als obs h'')
  note step = `heap_copy_loc a a' al h ob h'`
  from `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) (al # als) Ts`
  obtain T Ts' where [simp]: "Ts = T # Ts'"
    and "P,h \<turnstile> a@al : T" "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from `list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) (al # als) Ts`
  have "P,h \<turnstile> a'@al : T" "list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts'" by simp_all
  from step `hconf h` `P,h \<turnstile> a@al : T` `P,h \<turnstile> a'@al : T`
  have "hconf h'" by(rule hconf_heap_copy_loc_mono)
  moreover from step have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
  from `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'`
  have "list_all2 (\<lambda>al T. P,h' \<turnstile> a@al : T) als Ts'"
    by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h'`])
  moreover from `list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts'`
  have "list_all2 (\<lambda>al T. P,h' \<turnstile> a'@al : T) als Ts'"
    by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h'`])
  ultimately show ?case by(rule Cons)
qed

lemma hconf_heap_clone_mono:
  assumes wf: "wf_prog wf_md P"
  and "heap_clone P h a h' res"
  and "hconf h"
  shows "hconf h'"
using `heap_clone P h a h' res`
proof cases
  case ObjFail thus ?thesis using `hconf h`
    by(fastsimp intro: hconf_heap_ops_mono dest: typeof_addr_is_type)
next
  case ArrFail thus ?thesis using `hconf h`
    by(fastsimp intro: hconf_heap_ops_mono dest: typeof_addr_is_type)
next
  case (ObjClone C h'' a' FDTs obs)
  note FDTs = `P \<turnstile> C has_fields FDTs`
  let ?als = "map (\<lambda>((F, D), T). CField D F) FDTs"
  let ?Ts = "map snd FDTs"
  note `heap_copies a a' ?als h'' obs h'` 
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
  ultimately have "hconf h'" by(rule hconf_heap_copies_mono)
  thus ?thesis using ObjClone by simp
next
  case (ArrClone T n h'' a' obs)
  note [simp] = `n = array_length h a`
  let ?als = "map ACell [0..<n]"
  let ?Ts = "replicate n T"
  note `heap_copies a a' (map ACell [0..<n]) h'' obs h'`
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
  ultimately have "hconf h'" by(rule hconf_heap_copies_mono)
  thus ?thesis using ArrClone by simp
qed

theorem external_call_hconf:
  assumes wf: "wf_prog wf_md P"
  and major: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and minor: "P,h \<turnstile> a\<bullet>M(vs) : U" "hconf h"
  shows "hconf h'"
using major wf minor
proof cases
  case (RedInterrupt C)
  from `typeof_addr h a = \<lfloor>Class C\<rfloor>` `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P,h \<turnstile> a@interrupted_flag_loc : Boolean"
    by(auto intro!: addr_loc_type.intros wf_sub_Thread_has_interrupted_flag[OF wf])
  thus ?thesis using minor RedInterrupt by(force intro: hconf_heap_write_mono)
next
  case (RedWaitInterrupt C)
  from `typeof_addr h t = \<lfloor>Class C\<rfloor>` `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P,h \<turnstile> t@interrupted_flag_loc : Boolean"
    by(auto intro!: addr_loc_type.intros wf_sub_Thread_has_interrupted_flag[OF wf])
  thus ?thesis using minor RedWaitInterrupt by(force intro: hconf_heap_write_mono)
next
  case (RedWaitInterrupted C)
  from `typeof_addr h t = \<lfloor>Class C\<rfloor>` `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P,h \<turnstile> t@interrupted_flag_loc : Boolean"
    by(auto intro!: addr_loc_type.intros wf_sub_Thread_has_interrupted_flag[OF wf])
  thus ?thesis using minor RedWaitInterrupted by(force intro: hconf_heap_write_mono)
qed(fastsimp intro: hconf_heap_clone_mono[OF wf])+

end

context heap_base begin

primrec conf_extRet :: "'m prog \<Rightarrow> 'heap \<Rightarrow> extCallRet \<Rightarrow> ty \<Rightarrow> bool" where
  "conf_extRet P h (RetVal v) T = (P,h \<turnstile> v :\<le> T)"
| "conf_extRet P h (RetExc a) T = (P,h \<turnstile> Addr a :\<le> Class Throwable)"
| "conf_extRet P h RetStaySame T = True"

end

context heap begin

lemma red_external_conf_extRet:
  "\<lbrakk> wf_prog wf_md P; P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; P,h \<turnstile> a\<bullet>M(vs) : U; preallocated h \<rbrakk>
  \<Longrightarrow> conf_extRet P h' va U"
apply(frule red_external_hext)
apply(drule (1) preallocated_hext)
apply(auto elim!: red_external.cases external_WT.cases external_WT'.cases external_WT_defs_cases)
apply(auto simp add: conf_def intro: xcpt_subcls_Throwable dest!: hext_heap_write typeof_addr_heap_clone)
done

lemma red_external_aggr_conf_extRet:
  "\<lbrakk> wf_prog wf_md P; (ta, va, h') \<in> red_external_aggr P t a M vs h; P,h \<turnstile> a\<bullet>M(vs) : U; preallocated h \<rbrakk>
  \<Longrightarrow> conf_extRet P h' va U"
apply(frule (1) red_external_aggr_hext)
apply(frule (1) preallocated_hext)
apply(auto simp add: red_external_aggr_def split_beta split: split_if_asm)
apply(auto elim!: external_WT.cases external_WT'.cases external_WT_defs_cases)
apply(auto simp add: conf_def xcpt_subcls_Throwable)
apply(drule typeof_addr_heap_clone, simp)
apply(auto dest: typeof_InterruptedException simp add: xcpt_subcls_Throwable elim: external_WT_defs.cases)
done

end

context heap_progress begin

lemma red_external_wf_red:
  assumes wf: "wf_prog wf_md P"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and tconf: "P,h \<turnstile> t \<surd>t"
  and hconf: "hconf h"
  and wst: "wset s t = None \<or> (M = wait \<and> (\<exists>w. wset s t = \<lfloor>WokenUp w\<rfloor>))"
  obtains ta' va' h''
  where "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta'\<rightarrow>ext \<langle>va', h''\<rangle>" 
  and "final_thread.actions_ok' s t ta'"
  and "final_thread.actions_subset ta' ta"
proof(atomize_elim)
  from tconf obtain C where ht: "typeof_addr h t = \<lfloor>Class C\<rfloor>" 
    and sub: "P \<turnstile> C \<preceq>\<^sup>* Thread" by(fastsimp dest: tconfD)
  from wf sub have "P \<turnstile> C has interrupted_flag:Boolean in Thread" 
    by(rule wf_sub_Thread_has_interrupted_flag)
  with ht have "P,h \<turnstile> t@interrupted_flag_loc : Boolean"
    by(rule addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where read: "heap_read h t interrupted_flag_loc v"
    and "P,h \<turnstile> v :\<le> Boolean" by blast
  from `P,h \<turnstile> v :\<le> Boolean` obtain b
    where [simp]: "v = Bool b" by(auto simp add: conf_def)

  from heap_write_total[OF `P,h \<turnstile> t@interrupted_flag_loc : Boolean`, of "Bool False"]
    heap_write_total[OF `P,h \<turnstile> t@interrupted_flag_loc : Boolean`, of "Bool True"]
  obtain hT hF where writeT: "heap_write h t interrupted_flag_loc (Bool True) hT" 
    and writeF: "heap_write h t interrupted_flag_loc (Bool False) hF" by blast

  show "\<exists>ta' va' h'. P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta'\<rightarrow>ext \<langle>va', h'\<rangle> \<and> final_thread.actions_ok' s t ta' \<and> final_thread.actions_subset ta' ta"
  proof(cases "final_thread.actions_ok' s t ta")
    case True
    have "final_thread.actions_subset ta ta" by(rule final_thread.actions_subset_refl)
    with True red show ?thesis by blast
  next
    case False
    note [simp] = final_thread.actions_ok'_iff lock_ok_las'_def final_thread.cond_action_oks'_subset_Join
      final_thread.actions_subset_iff ta_upd_simps
    note [rule del] = subsetI
    note [intro] = collect_locks'_subset_collect_locks red_external.intros[simplified]

    show ?thesis
    proof(cases "wset s t")
      case (Some w)[simp]
      with wst obtain w' where [simp]: "w = WokenUp w'" "M = wait" by auto
      from red have [simp]: "vs = []" by(auto elim: red_external.cases)
      show ?thesis
      proof(cases w')
        case WSInterrupted[simp]
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub> Interrupted \<rbrace>\<lbrace>\<^bsub>o\<^esub> WriteMem t interrupted_flag_loc (Bool False)\<rbrace>"
        have "final_thread.actions_ok' s t ?ta'" by(simp add: wset_actions_ok_def)
        moreover have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply final_thread.collect_cond_actions_def)
        moreover from RedWaitInterrupted ht sub read writeF 
        have "\<exists>va h'. P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by auto
        ultimately show ?thesis by blast
      next
        case WSNotified[simp]
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notified \<rbrace>"
        have "final_thread.actions_ok' s t ?ta'" by(simp add: wset_actions_ok_def)
        moreover have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply final_thread.collect_cond_actions_def)
        moreover from RedWaitNotified ht sub
        have "\<exists>va h'. P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by auto
        ultimately show ?thesis by blast
      qed
    next
      case None

      from red False show ?thesis
      proof cases
        case (RedNewThread C)
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a (C, run, a) h\<rbrace>\<lbrace>\<^bsub>o\<^esub>ThreadStart a\<rbrace>`
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists a\<rbrace>"
        from ta False None have "final_thread.actions_ok' s t ?ta'" by(auto)
        moreover from ta have "final_thread.actions_subset ?ta' ta" by(auto)
        ultimately show ?thesis using RedNewThread by(fastsimp)
      next
        case RedNewThreadFail
        then obtain va' h' x where "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -\<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a x h'\<rbrace>\<lbrace>\<^bsub>o\<^esub>ThreadStart a\<rbrace>\<rightarrow>ext \<langle>va', h'\<rangle>" by(fastsimp)
        moreover from `ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists a\<rbrace>` False None
        have "final_thread.actions_ok' s t \<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a x h'\<rbrace>\<lbrace>\<^bsub>o\<^esub>ThreadStart a\<rbrace>" by(auto)
        moreover from `ta = \<epsilon>\<lbrace>\<^bsub>t\<^esub>ThreadExists a\<rbrace>`
        have "final_thread.actions_subset \<epsilon>\<lbrace>\<^bsub>t\<^esub>NewThread a x h'\<rbrace>\<lbrace>\<^bsub>o\<^esub>ThreadStart a\<rbrace> ta" by(auto)
        ultimately show ?thesis by blast
      next
        case RedJoin thus ?thesis using None by fastsimp
      next
        case RedInterrupt thus ?thesis using None
          by(fastsimp simp del: split_paired_Ex simp add: wset_actions_ok_def)
      next
        case RedWaitInterrupt
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), WriteMem t interrupted_flag_loc (Bool False)\<rbrace>`
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
        from ta False None have "\<not> may_lock ((locks s)\<^sub>f a) t \<or> \<not> has_lock ((locks s)\<^sub>f a) t"
	  by(auto simp add: lock_actions_ok'_iff finfun_upd_apply split: split_if_asm dest: may_lock_t_may_lock_unlock_lock_t)
        hence "\<not> has_lock ((locks s)\<^sub>f a) t" by(metis has_lock_may_lock)
        hence "final_thread.actions_ok' s t ?ta'" using None
          by(auto simp add: lock_actions_ok'_iff finfun_upd_apply)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply)
        moreover from RedWaitInterrupt obtain va h' where "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
        ultimately show ?thesis by blast
      next
        case RedWait
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), SyncUnlock a\<rbrace>`
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
        from ta False None have "\<not> may_lock ((locks s)\<^sub>f a) t \<or> \<not> has_lock ((locks s)\<^sub>f a) t"
	  by(auto simp add: lock_actions_ok'_iff finfun_upd_apply wset_actions_ok_def split: split_if_asm dest: may_lock_t_may_lock_unlock_lock_t)
        hence "\<not> has_lock ((locks s)\<^sub>f a) t" by(metis has_lock_may_lock)
        hence "final_thread.actions_ok' s t ?ta'" using None
          by(auto simp add: lock_actions_ok'_iff finfun_upd_apply)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply)
        moreover from RedWait obtain va h' where "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
        ultimately show ?thesis by blast
      next
        case RedWaitFail
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>`
        let ?ta' = "if b
                   then \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>
                         \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True),
                            WriteMem t interrupted_flag_loc (Bool False)\<rbrace>
                   else \<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>
                         \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), SyncUnlock a\<rbrace>"
        from ta False None have "has_lock ((locks s)\<^sub>f a) t"
          by(auto simp add: finfun_upd_apply split: split_if_asm)
        hence "final_thread.actions_ok' s t ?ta'" using None
          by(auto simp add: finfun_upd_apply wset_actions_ok_def intro: has_lock_may_lock)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply)
        moreover from RedWaitFail ht sub read writeF
        obtain va h' where "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(cases b)(auto)
        ultimately show ?thesis by blast
      next
        case RedWaitNotified
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub>Notified\<rbrace>`
        let ?ta' = "if has_lock ((locks s)\<^sub>f a) t
                   then (if b 
                         then \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>
                               \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True),
                                  WriteMem t interrupted_flag_loc (Bool False)\<rbrace>
                         else \<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>
                               \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), SyncUnlock a\<rbrace>)
                   else \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
        have "final_thread.actions_ok' s t ?ta'"
          using None by(auto simp add: finfun_upd_apply wset_actions_ok_def intro: has_lock_may_lock)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply final_thread.collect_cond_actions_def)
        moreover from RedWaitNotified ht sub read writeF 
          RedWait[of h t C P a] RedWaitInterrupt[of h t C P hF a] RedWaitFail[of P t h a]
        have "\<exists>va h'. P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by fastsimp
        ultimately show ?thesis by blast
      next
        case RedWaitInterrupted
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub>Interrupted\<rbrace>\<lbrace>\<^bsub>o\<^esub> WriteMem t interrupted_flag_loc (Bool False)\<rbrace>`
        let ?ta' = "if has_lock ((locks s)\<^sub>f a) t
                   then (if b 
                         then \<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>
                               \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True),
                                  WriteMem t interrupted_flag_loc (Bool False)\<rbrace>
                         else \<epsilon>\<lbrace>\<^bsub>w\<^esub>Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>
                               \<lbrace>\<^bsub>o\<^esub> ReadMem t interrupted_flag_loc (Bool True), SyncUnlock a\<rbrace>)
                   else \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
        have "final_thread.actions_ok' s t ?ta'" using None
          by(auto simp add: finfun_upd_apply wset_actions_ok_def intro: has_lock_may_lock)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply final_thread.collect_cond_actions_def)
        moreover from RedWaitInterrupted ht sub read writeF
          RedWait[of h t C P a] RedWaitInterrupt[of h t C P hF a] RedWaitFail[of P t h a]
        have "\<exists>va h'. P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by fastsimp
        ultimately show ?thesis by blast
      next
        case RedNotify
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub>Notify a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>`
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
        from ta False None have "\<not> may_lock ((locks s)\<^sub>f a) t \<or> \<not> has_lock ((locks s)\<^sub>f a) t"
	  by(auto simp add: lock_actions_ok'_iff finfun_upd_apply wset_actions_ok_def split: split_if_asm dest: may_lock_t_may_lock_unlock_lock_t)
        hence "\<not> has_lock ((locks s)\<^sub>f a) t" by(metis has_lock_may_lock)
        hence "final_thread.actions_ok' s t ?ta'" using None
          by(auto simp add: lock_actions_ok'_iff finfun_upd_apply)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply)
        moreover from RedNotify obtain va h' where "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
        ultimately show ?thesis by blast
      next
        case RedNotifyFail
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>`
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub>Notify a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>"
        from ta False None have "has_lock ((locks s)\<^sub>f a) t"
          by(auto simp add: finfun_upd_apply split: split_if_asm)
        hence "final_thread.actions_ok' s t ?ta'" using None
          by(auto simp add: finfun_upd_apply simp add: wset_actions_ok_def intro: has_lock_may_lock)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply)
        moreover from RedNotifyFail obtain va h' where "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
        ultimately show ?thesis by blast
      next
        case RedNotifyAll
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>w\<^esub>NotifyAll a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>`
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
        from ta False None have "\<not> may_lock ((locks s)\<^sub>f a) t \<or> \<not> has_lock ((locks s)\<^sub>f a) t"
	  by(auto simp add: lock_actions_ok'_iff finfun_upd_apply wset_actions_ok_def split: split_if_asm dest: may_lock_t_may_lock_unlock_lock_t)
        hence "\<not> has_lock ((locks s)\<^sub>f a) t" by(metis has_lock_may_lock)
        hence "final_thread.actions_ok' s t ?ta'" using None
          by(auto simp add: lock_actions_ok'_iff finfun_upd_apply)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply)
        moreover from RedNotifyAll obtain va h' where "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
        ultimately show ?thesis by blast
      next
        case RedNotifyAllFail
        note ta = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>`
        let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub>NotifyAll a\<rbrace>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>"
        from ta False None have "has_lock ((locks s)\<^sub>f a) t"
          by(auto simp add: finfun_upd_apply split: split_if_asm)
        hence "final_thread.actions_ok' s t ?ta'" using None
          by(auto simp add: finfun_upd_apply wset_actions_ok_def intro: has_lock_may_lock)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: collect_locks'_def finfun_upd_apply)
        moreover from RedNotifyAllFail obtain va h' where "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -?ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by(fastsimp)
        ultimately show ?thesis by blast
      qed(auto simp add: None)
    qed
  qed
qed

end

end