(*  Title:      JinjaThreads/MM/JMM_J.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{JMM instantiation with Jinja source code} *}

theory JMM_J imports
  "JMM_Common"
  "../J/ProgressThreaded"
  "../Compiler/J0"
begin

sublocale J_heap_base < red_mthr!: 
  if_\<tau>multithreaded_wf
    final_expr
    "mred P"
    convert_RA
    "\<tau>MOVE P"
  for P
by(unfold_locales)

sublocale J_heap_base < red_mthr_if!: jmm_\<tau>multithreaded
  "red_mthr.init_fin_final"
  "red_mthr.init_fin P"
  "map NormalAction \<circ> convert_RA"
  "red_mthr.init_fin_\<tau>move P"
.

section {* Initialisations precede reads *}
  
context J_heap begin

lemma red_New_typeof_addrD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr (hp s) a = None \<and> typeof_addr (hp s') a = Some (ty_of_htype x)"
  and reds_New_typeof_addrD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr (hp s) a = None \<and> typeof_addr (hp s') a = Some (ty_of_htype x)"
apply(induct rule: red_reds.inducts)
apply(auto dest: new_obj_SomeD new_arr_SomeD red_external_New_typeof_addrD)
done

lemma red_NewArr_lengthD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length (hp s') a = n"
  and reds_NewARr_lengthD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length (hp s') a = n"
apply(induct rule: red_reds.inducts)
apply(auto dest: new_arr_SomeD red_external_NewArr_lengthD)
done

lemma red_New_same_addr_same:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
  and reds_New_same_addr_same:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(induct rule: red_reds.inducts)
apply(auto dest: red_external_New_same_addr_same)
done

lemma assumes wf: "wf_prog wf_md P"
  shows red_read_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s \<turnstile> ad@al : T'"
  and reds_read_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s \<turnstile> ad@al : T'"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case RedAAcc thus ?case
    by(fastsimp intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def)
next
  case RedFAcc thus ?case
    by(fastsimp intro: addr_loc_type.intros dest: typeof_addr_eq_Some_conv)
next
  case RedCallExternal thus ?case
    by(auto intro: red_external_read_mem_typeable[OF wf])
qed auto

lemma assumes minimal: "heap_ops_typeof_minimal"
  shows red_create_object:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; typeof_addr (hp s') a = \<lfloor>T\<rfloor>; typeof_addr (hp s) a = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> hp s' \<turnstile>a a : CTn"
  and reds_create_object:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; typeof_addr (hp s') a = \<lfloor>T\<rfloor>; typeof_addr (hp s) a = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> hp s' \<turnstile>a a : CTn"
proof(induct rule: red_reds.inducts)
  case RedNewArray thus ?case
    apply -
    apply(frule new_arr_SomeD)
    apply(drule heap_ops_typeof_minimalD'[OF minimal])
    apply(auto split: split_if_asm)
    done
qed(auto dest: heap_ops_typeof_minimalD'[OF minimal] new_arr_SomeD red_external_new_heap_ops_obs[OF minimal] split: split_if_asm)

end

context J_conf_read begin

lemma J_heap_jmm_aux: 
  assumes wf: "wf_J_prog P"
  shows "heap_jmm_aux empty_heap new_obj new_arr typeof_addr array_length heap_write
                      final_expr (mred P) (\<tau>MOVE P) (\<lambda>t x m. P,m \<turnstile> t \<surd>t) (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x) P"
proof -  
  interpret lifting_inv
    final_expr
    "mred P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile> t \<surd>t"
    "\<lambda>ET t (e, x) m. sconf_type_ok ET e m x"
    using wf by(rule lifting_inv_sconf_subject_ok)

  show ?thesis
    apply(unfold_locales)
    apply(fastsimp dest: red_hext_incr)
    apply(fastsimp dest: red_New_typeof_addrD)
    apply(fastsimp dest: red_New_same_addr_same)
    apply(fastsimp dest: red_create_object)
    apply(fastsimp simp add: sconf_type_ok_def sconf_def type_ok_def dest: red_read_typeable[OF wf])
    done
qed

lemma JMM_inst_aux: 
  assumes wf_prog: "wf_J_prog P"
  and minimal: "heap_ops_typeof_minimal"
  and start_heap: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  shows "executions_sc (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` 
                         red_mthr.if.\<E> P (init_fin_lift_state Running (J_start_state P C M vs)))
                        P"
proof -
  let ?wt_ok = "\<lambda>ET t (e, x) m. sconf_type_ok ET e m x"
  let ?thread_ok = "\<lambda>t x m. P,m \<turnstile> t \<surd>t"
  let ?start_state = "init_fin_lift_state Running (J_start_state P C M vs)"
  let ?ET_start = "J_sconf_type_ET_start P C M"

  interpret heap_jmm_aux
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
    final_expr
    "mred P"
    "\<tau>MOVE P"
    "?thread_ok"
    "?wt_ok"
    P
    using wf_prog by(rule J_heap_jmm_aux)

  note minimal start_heap
  moreover from wf_prog start_heap sees conf
  have "ts_inv (init_fin_lift_inv ?wt_ok) ?ET_start (thr ?start_state) (shr ?start_state)"
    unfolding ts_inv_init_fin_lift_inv_init_fin_lift_state
    by(rule sconf_type_ts_ok_J_start_state)
  moreover have "ts_ok (init_fin_lift ?thread_ok) (thr ?start_state) (shr ?start_state)"
    using start_heap unfolding ts_ok_init_fin_lift_init_fin_lift_state
    by(rule thread_conf_start_state)
  ultimately show ?thesis
    unfolding init_fin_lift_state_start_state by(rule JMM_inst_aux)
qed

section {* Locale @{text exeuctions} *}

lemma assumes wf: "wf_prog wf_md P"
  shows red_write_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; hconf (hp s); WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s' \<turnstile> ad@al : T' \<and> P,hp s' \<turnstile> v :\<le> T'"
  and reds_write_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; hconf (hp s); WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s' \<turnstile> ad@al : T' \<and> P,hp s' \<turnstile> v :\<le> T'"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case RedAAss thus ?case
    by(fastsimp intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def conf_def hext_arrD dest!: hext_heap_write intro: typeof_addr_hext_mono hext_typeof_mono)
next
  case RedFAss thus ?case
    by(fastsimp intro: addr_loc_type.intros simp add: conf_def dest: typeof_addr_eq_Some_conv dest!: hext_heap_write elim: typeof_addr_hext_mono hext_typeof_mono)
next
  case RedCallExternal thus ?case
    by(auto intro: red_external_write_typeable[OF wf])
qed auto

lemma J_heap_jmm:
  assumes wf: "wf_J_prog P"
  shows "heap_jmm empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf
                  final_expr (mred P) (\<tau>MOVE P) (\<lambda>t x m. P,m \<turnstile> t \<surd>t) (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x) P"
proof -
  interpret heap_jmm_aux empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
                       final_expr "mred P" "\<tau>MOVE P" "\<lambda>t x m. P,m \<turnstile> t \<surd>t" "\<lambda>ET t (e, x) m. sconf_type_ok ET e m x" P
    using wf by(rule J_heap_jmm_aux)

  show ?thesis
    by(unfold_locales)(fastsimp dest: red_NewArr_lengthD red_write_typeable[OF wf] simp add: sconf_type_ok_def type_ok_def sconf_def)+
qed

end

interpretation jmm'!: J_typesafe 
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
by unfold_locales

abbreviation jmm'_red' :: "J_prog \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> JMM_heap \<times> locals \<Rightarrow> JMM_heap J_thread_action \<Rightarrow> expr \<Rightarrow> JMM_heap \<times> locals \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
where "jmm'_red' P \<equiv> jmm'.red' P P"

abbreviation jmm'_reds' :: "J_prog \<Rightarrow> nat \<Rightarrow> expr list \<Rightarrow> JMM_heap \<times> locals \<Rightarrow> JMM_heap J_thread_action \<Rightarrow> expr list \<Rightarrow> JMM_heap \<times> locals \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' ((1\<langle>_,/_\<rangle>) [-_\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
where "jmm'_reds' P \<equiv> jmm'.reds' P P"

notation jmm'.WTrt_syntax ("_,_,_ \<turnstile>jmm' _ : _"   [51,51,51]50)
notation jmm'.WTrts_syntax ("_,_,_ \<turnstile>jmm' _ [:] _"   [51,51,51]50)

subsection {* Cut and update *}

declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

lemma assumes wf: "wf_prog wf_md P"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile>jmm' ad@al : T \<and> P,shr s \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,shr s \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and hconf: "P \<turnstile>jmm' shr s \<surd>"
  shows red_cut_and_update:
  "\<lbrakk> P,t \<turnstile>jmm' \<langle>e, (shr s, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>; P,E,shr s \<turnstile>jmm' e : T;
    jmm'.red_mthr.if.actions_ok s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta' e'' xs'' h''. P,t \<turnstile>jmm' \<langle>e, (shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e'', (h'', xs'')\<rangle> \<and> 
           jmm'.red_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
  and reds_cut_and_update:
  "\<lbrakk> P,t \<turnstile>jmm' \<langle>es, (shr s, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle>; P,E,shr s \<turnstile>jmm' es [:] Ts;
    jmm'.red_mthr.if.actions_ok s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta' es'' xs'' h''. P,t \<turnstile>jmm' \<langle>es, (shr s, xs)\<rangle> [-ta'\<rightarrow>] \<langle>es'', (h'', xs'')\<rangle> \<and> 
           jmm'.red_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
proof(induct e hxs\<equiv>"(shr s, xs)" ta e' hxs'\<equiv>"(h', xs')" 
         and es hxs\<equiv>"(shr s, xs)" ta es' hxs'\<equiv>"(h', xs')"
      arbitrary: xs xs' E T and xs xs' E Ts rule: jmm'.red_reds.inducts)
  case (RedInstanceOf v U b T)
  thus ?case by(intro exI conjI)(rule jmm'.RedInstanceOf, simp_all)
next
  case (RedAAcc a U i v e)
  hence adal: "P,shr s \<turnstile>jmm' a@ACell (nat (sint i)) : U"
    by(auto intro: jmm'.addr_loc_type.intros simp add: nat_less_iff word_sle_def)
  then obtain b v' where bv': "vs (a, ACell (nat (sint i))) = \<lfloor>(v', b)\<rfloor>"
    using subsetD[OF dom_vs, where c="(a, ACell (nat (sint i)))"] by fastsimp
  with adal have "P,shr s \<turnstile>jmm' v' :\<le> U" by(auto dest: vs jmm'.addr_loc_type_fun)
  with adal have "jmm_heap_read' P (shr s) a (ACell (nat (sint i))) v'"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  with bv' `jmm_typeof_addr (shr s) a = \<lfloor>U\<lfloor>\<rceil>\<rfloor>` `0 <=s i` `sint i < int (jmm_array_length (shr s) a)` 
    `jmm'.red_mthr.if.actions_ok s t \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem a (ACell (nat (sint i))) v\<rbrace>`
  show ?case by(fastsimp intro: jmm'.RedAAcc)
next
  case (RedFAcc a D F v)
  hence adal: "P,shr s \<turnstile>jmm' a@CField D F : T"
    by(auto dest: jmm'.typeof_addr_eq_Some_conv intro: jmm'.addr_loc_type.intros)
  then obtain b v' where bv': "vs (a, CField D F) = \<lfloor>(v', b)\<rfloor>"
    using subsetD[OF dom_vs, where c="(a, CField D F)"] by fastsimp
  with adal have "P,shr s \<turnstile>jmm' v' :\<le> T" by(auto dest: vs jmm'.addr_loc_type_fun)
  with adal have "jmm_heap_read' P (shr s) a (CField D F) v'"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  with bv' `jmm'.red_mthr.if.actions_ok s t \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem a (CField D F) v\<rbrace>`
  show ?case by(fastsimp intro: jmm'.RedFAcc)
next
  case (RedCallExternal a U M vs ta' va h' ta e')
  from `P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs),hp (shr s, xs)\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>`
  have red: "P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs),shr s\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by simp
  from RedCallExternal have "jmm'.red_mthr.if.actions_ok s t ta'" by simp
  from jmm'.red_mthr.if.red_external_cut_and_update[OF wf vs dom_vs red this hconf, of "\<lambda>_ _ _ b. b"]
    `jmm_typeof_addr (hp (shr s, xs)) a = \<lfloor>U\<rfloor>` `is_external_call P U M` `ta = extTA2J P ta'`
  show ?case by(fastsimp intro: jmm'.red_reds.RedCallExternal)
next 
  case NewArrayRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next 
  case CastRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case InstanceOfRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case BinOpRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case BinOpRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case LAssRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAccRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAccRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAssRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAssRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAssRed3 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case ALengthRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case FAccRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case FAssRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case FAssRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case CallObj thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case CallParams thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case BlockRed thus ?case by(fastsimp intro: jmm'.red_reds.intros)
next
  case SynchronizedRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case SynchronizedRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case SeqRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case CondRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case ThrowRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case TryRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case ListRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case ListRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
qed(fastsimp intro: jmm'.red_reds.intros)+

declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

lemma cut_and_update:
  assumes wf_prog: "wf_J_prog P"
  and start_heap: "jmm'.start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,jmm'.start_heap \<turnstile>jmm' vs [:\<le>] Ts"
  shows "jmm'.red_mthr_if.cut_and_update P (init_fin_lift_state Running (jmm'.J_start_state P C M vs)) 
                                        (mrw_values P empty (map snd (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)))"
  (is "jmm'.red_mthr_if.cut_and_update _ ?start_state ?start_vs")
proof(rule jmm'.red_mthr_if.cut_and_updateI)
  fix ttas s' t x ta x' m'
  assume \<tau>Red: "jmm'.red_mthr.if.mthr.\<tau>rtrancl3p P P ?start_state ttas s'"
    and sc: "ta_seq_consist P ?start_vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and ts't: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "jmm'.red_mthr.init_fin P P t (x, shr s') ta (x', m')"
    and aok: "jmm'.red_mthr.if.actions_ok s' t ta"
    and n\<tau>: "\<not> jmm'.red_mthr.init_fin_\<tau>move P (x, shr s') ta (x', m')"

  let ?conv = "\<lambda>ttas. concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)"
  let ?vs' = "mrw_values P ?start_vs (?conv ttas)"
  let ?wt_ok = "init_fin_lift_inv (\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x)"
  let ?thread_ok = "init_fin_lift (\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t)"
  let ?ET_start = "jmm'.J_sconf_type_ET_start P C M"
  let ?start_obs = "map snd (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)"

  interpret heap_jmm
    jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm_heap_read' P" "jmm_heap_write' P" "jmm_hconf P"
    final_expr
    "jmm'.mred P P"
    "jmm'.\<tau>MOVE P"
    "\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t"
    "\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x"
    P
    using wf_prog by(rule jmm'.J_heap_jmm)

  from jmm'.sconf_type_ts_ok_J_start_state[OF wf_prog start_heap sees conf]
  have wt: "ts_inv ?wt_ok ?ET_start (thr ?start_state) (shr ?start_state)" by(simp)

  from start_heap have thread_ok: "ts_ok ?thread_ok (thr ?start_state) (shr ?start_state)"
    by(simp add: jmm'.thread_conf_start_state)

  from \<tau>Red wt thread_ok obtain ET'
    where wt': "ts_inv ?wt_ok ET' (thr s') (shr s')"
    by(blast dest: wfix_if.redT_\<tau>rtrancl3p_invariant)

  from \<tau>Red have hext: "shr ?start_state \<unlhd>jmm' shr s'"
    by(rule init_fin_\<tau>rtrancl3p_hext)

  show "\<exists>ta' x'' m''. jmm'.red_mthr.init_fin P P t (x, shr s') ta' (x'', m'') \<and>
                      jmm'.red_mthr.if.actions_ok s' t ta' \<and>
                      \<not> jmm'.red_mthr.init_fin_\<tau>move P (x, shr s') ta' (x'', m'') \<and>
                      ta_seq_consist P ?vs' (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                      eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs'"
  proof(cases "ta_seq_consist P ?vs' (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)")
    case True
    hence "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ?vs'"
      by(rule ta_seq_consist_imp_eq_upto_seq_inconsist_refl)
    with red aok n\<tau> True show ?thesis by blast
  next
    case False
    with red obtain e xs e' xs' ta'
      where x: "x = (Running, e, xs)" and x': "x' = (Running, e', xs')"
      and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
      and red': "P,t \<turnstile>jmm' \<langle>e, (shr s', xs)\<rangle> -ta'\<rightarrow> \<langle>e', (m', xs')\<rangle>"
      by cases fastsimp+

    from ts't wt' x obtain E T where wte: "P,E,shr s' \<turnstile>jmm' e : T"
      and hconf: "P \<turnstile>jmm' shr s' \<surd>"
      by(auto dest!: ts_invD simp add: jmm'.sconf_type_ok_def jmm'.sconf_def jmm'.type_ok_def)

    have aok': "jmm'.red_mthr.if.actions_ok s' t ta'"
      using aok unfolding ta by simp

    { fix ad al v b
      assume "?vs' (ad, al) = \<lfloor>(v, b)\<rfloor>"
      moreover
      { assume "?start_vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
        hence "\<exists>T. P,jmm'.start_heap \<turnstile>jmm' ad@al : T \<and> P,jmm'.start_heap \<turnstile>jmm' v :\<le> T" 
          by -(rule heap.mrw_values_start_heap_obs_typeable[OF jmm'_heap], simp add: lift_start_obs_def o_def)
        hence "\<exists>T. P,shr ?start_state \<turnstile>jmm' ad@al : T \<and> P,shr ?start_state \<turnstile>jmm' v :\<le> T"
          by(simp add: init_fin_lift_state_conv_simps jmm'.start_state_def split_beta) }
      ultimately have "\<exists>T. P,shr s' \<turnstile>jmm' ad@al : T \<and> P,shr s' \<turnstile>jmm' v :\<le> T"
        using \<tau>Red thread_ok wt by -(rule \<tau>RedT_mrw_values_typeable) }
    note wt_vs = this

    { fix ad al T
      assume adal: "P,shr s' \<turnstile>jmm' ad@al : T"
      then obtain U where U: "jmm_typeof_addr (shr s') ad = \<lfloor>U\<rfloor>" by cases
      have "(ad, al) \<in> dom ?vs'"
      proof(cases "jmm_typeof_addr (shr ?start_state) ad")
        case None
        from redT_\<tau>rtrancl3p_created_objects[OF jmm'_heap_ops_typeof_minimal \<tau>Red U None]
        obtain CTn where CTn: "NormalAction (NewHeapElem ad CTn) \<in> set (?conv ttas)"
          and "U = ty_of_htype CTn" "jmm'.htypeof_addr (shr s') ad CTn" by(fastsimp)
        with U adal have "(ad, al) \<in> action_loc_aux P (NormalAction (NewHeapElem ad CTn))"
          by(cases CTn)(fastsimp elim!: jmm'.addr_loc_type.cases)+
        from mrw_values_new_actionD[OF CTn _ this, where ?vs0.0="?start_vs"]
        show ?thesis by auto
      next
        case (Some U')
        hence "ad \<in> set jmm'.start_addrs"
          
          using subsetD[OF jmm'.dom_typeof_addr_start_heap_eq_start_addrs[OF jmm'_heap_ops_typeof_minimal, THEN equalityD1], where c="ad"]
          by(auto simp add: init_fin_lift_state_conv_simps jmm'.start_state_def split_def)
        from jmm'.start_addrs_NewHeapElem_start_heap_obsD[OF this]
        obtain CTn where CTn: "NewHeapElem ad CTn \<in> set jmm'.start_heap_obs" ..
        hence CTn': "NormalAction (NewHeapElem ad CTn) \<in> set ?start_obs" by(auto simp add: image_image)
        have "(ad, al) \<in> action_loc_aux P (NormalAction (NewHeapElem ad CTn))"
        proof(cases CTn)
          case (Class_type C)
          with CTn have "jmm_typeof_addr jmm'.start_heap ad = \<lfloor>Class C\<rfloor>"
            by(auto dest: jmm'.NewObj_start_heap_obsD)
          with hext have "jmm_typeof_addr (shr s') ad = \<lfloor>Class C\<rfloor>"
            by(simp add: init_fin_lift_state_conv_simps jmm'.start_state_def split_def jmm'.typeof_addr_hext_mono)
          with adal U Class_type show ?thesis by cases auto
        next
          case (Array_type T n)
          with CTn have "jmm_typeof_addr jmm'.start_heap ad = \<lfloor>Array T\<rfloor>"
            and "jmm_array_length jmm'.start_heap ad = n"
            by(auto dest: jmm'.NewArr_start_heap_obsD)
          with hext have "jmm_typeof_addr (shr s') ad = \<lfloor>Array T\<rfloor>"
            and "jmm_array_length (shr s') ad = n"
            by(auto simp add: init_fin_lift_state_conv_simps jmm'.start_state_def split_def dest: jmm'.hext_arrD)
          with adal U Array_type show ?thesis by cases auto
        qed
        from mrw_values_new_actionD[OF CTn' _ this, where ?vs0.0=empty]
        have "(ad, al) \<in> dom ?start_vs" by auto
        also note mrw_values_dom_mono
        finally show ?thesis .
      qed }
    hence "{(ad, al). \<exists>T. P,shr s' \<turnstile>jmm' ad@al : T} \<subseteq> dom ?vs'" by blast

    from red_cut_and_update[OF wf_prog wt_vs this hconf red' wte aok', where ?b3="\<lambda>_ _ _ b. b"]
    obtain ta'' e'' xs'' h''
      where red'': "P,t \<turnstile>jmm' \<langle>e, (shr s', xs)\<rangle> -ta''\<rightarrow> \<langle>e'', (h'', xs'')\<rangle>"
      and aok'': "jmm'.red_mthr.if.actions_ok s' t ta''"
      and sc'': "ta_seq_consist P ?vs' (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
      and eq'': "eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) ?vs'"
      by blast

    from n\<tau> x x' have "\<not> jmm'.\<tau>move0 P (shr s') e \<or> ta \<noteq> \<epsilon>"
      by(auto intro: jmm'.red_mthr.init_fin_\<tau>move.intros)
    with red x x' have "\<not> jmm'.\<tau>move0 P (shr s') e"
      by(auto dest: jmm'.red_\<tau>_taD[where extTA="extTA2J P", simplified])
    hence n\<tau>'': "\<not> jmm'.\<tau>MOVE P ((e, xs), shr s') ta'' ((e'', xs''), h'')" by auto 

    let ?x' = "(Running, e'', xs'')"
    let ?ta' = "convert_TA_initial (convert_obs_initial ta'')"
    from red'' have "jmm'.red_mthr.init_fin P P t (x, shr s') ?ta' (?x', h'')"
      unfolding x by -(rule jmm'.red_mthr.init_fin.NormalAction, simp)
    moreover from aok'' have "jmm'.red_mthr.if.actions_ok s' t ?ta'" by simp
    moreover from n\<tau>'' have "\<not> jmm'.red_mthr.init_fin_\<tau>move P (x, shr s') ?ta' (?x', h'')"
      unfolding x by auto
    moreover from sc'' have "ta_seq_consist P ?vs' (llist_of \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub>)" by simp
    moreover from eq'' have "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> ?vs'" unfolding ta by simp
    ultimately show ?thesis by blast
  qed
qed

lemma JMM_inst: 
  assumes wf_prog: "wf_J_prog P"
  and minimal: "jmm'_heap_ops_typeof_minimal P"
  and start_heap: "jmm'.start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,jmm'.start_heap \<turnstile>jmm' vs [:\<le>] Ts"
  shows "executions (lappend (llist_of (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)) ` 
                     jmm'.red_mthr.if.\<E> P P (init_fin_lift_state Running (jmm'.J_start_state P C M vs)))
                    P"
  (is "executions ?E _")
proof -
  let ?start_state = "init_fin_lift_state Running (jmm'.J_start_state P C M vs)"

  interpret heap_jmm
    jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm_heap_read' P" "jmm_heap_write' P" "jmm_hconf P"
    final_expr
    "jmm'.mred P P"
    "jmm'.\<tau>MOVE P"
    "\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t"
    "\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x"
    P
    using wf_prog by(rule jmm'.J_heap_jmm)


  interpret Jjmm!: executions_sc ?E P
    using wf_prog minimal start_heap sees conf by(rule jmm'.JMM_inst_aux)

  interpret Jinja_executions_aux
    final_expr
    "jmm'.mred P P"
    "jmm'.\<tau>MOVE P"
    "jmm'.start_heap_obs"
    "jmm'.start_tid"
    "?start_state" P
    by unfold_locales(auto simp add: jmm'.start_heap_obs_not_Read jmm'.start_state_def init_fin_lift_state_def split_beta split: split_if_asm intro!: Status_no_wait_locksI)

  from wf_prog start_heap sees conf
  show ?thesis
    by(rule executions[unfolded start_heap_obs_def, OF cut_and_update])
qed

end