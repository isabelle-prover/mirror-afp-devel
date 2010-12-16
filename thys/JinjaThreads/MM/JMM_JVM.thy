(*  Title:      JinjaThreads/MM/JMM_JVM.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{JMM instantiation with Jinja byte code} *}

theory JMM_JVM imports
  "JMM_Common"
  "../BV/BVProgressThreaded"
  "../Compiler/JVMTau"
begin

sublocale JVM_heap_base < execd_mthr!: 
  if_\<tau>multithreaded_wf
    JVM_final
    "mexecd P"
    convert_RA
    "\<tau>MOVE2 P"
  for P
by(unfold_locales)

sublocale JVM_heap_base < execd_mthr_if!: jmm_\<tau>multithreaded
  "execd_mthr.init_fin_final"
  "execd_mthr.init_fin P"
  "map NormalAction \<circ> convert_RA"
  "execd_mthr.init_fin_\<tau>move P"
.

section {* Locale @{text executions_aux} *}

context JVM_heap begin

lemma exec_instr_New_typeof_addrD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h a = None \<and> typeof_addr h' a = Some (ty_of_htype x)"
apply(cases i)
apply(auto dest: new_obj_SomeD new_arr_SomeD split: prod.split_asm split_if_asm)
apply(auto split: extCallRet.split_asm dest: red_external_aggr_New_typeof_addrD)
done

lemma exec_New_typeof_addrD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec P t (xcp, h, frs); NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h a = None \<and> typeof_addr h' a = Some (ty_of_htype x)"
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto dest: exec_instr_New_typeof_addrD)
done

lemma exec_1_d_New_typeof_addrD:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h a = None \<and> typeof_addr h' a = Some (ty_of_htype x)"
by(erule jvmd_NormalE)(rule exec_New_typeof_addrD)

lemma exec_instr_NewArr_lengthD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length h' a = n"
apply(cases i)
apply(auto dest: new_arr_SomeD split: prod.split_asm split_if_asm)
apply(auto split: extCallRet.split_asm dest: red_external_aggr_NewArr_lengthD)
done

lemma exec_NewArr_lengthD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec P t (xcp, h, frs); NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length h' a = n"
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto dest: exec_instr_NewArr_lengthD)
done

lemma exec_1_d_NewArr_lengthD:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length h' a = n"
by(erule jvmd_NormalE)(rule exec_NewArr_lengthD)

lemma exec_instr_New_same_addr_same:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr ins P t h stk loc C M pc frs;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(cases ins)
apply(auto split: prod.split_asm split_if_asm)
apply(auto split: extCallRet.split_asm dest: red_external_aggr_New_same_addr_same)
done

lemma exec_New_same_addr_same:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec P t (xcp, h, frs); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto dest: exec_instr_New_same_addr_same)
done

lemma exec_1_d_New_same_addr_same:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(erule jvmd_NormalE)(rule exec_New_same_addr_same)

lemma exec_instr_read_typeable:
  assumes wf: "wf_prog wf_md P"
  and exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and tconf: "P,h \<turnstile> t \<surd>t"
  shows "\<exists>T'. P,h \<turnstile> ad@al : T'"
using exec check read
proof(cases i)
  case ALoad
  with assms show ?thesis
    by(fastsimp simp add: split_beta is_Ref_def nat_less_iff word_sless_alt intro: addr_loc_type.intros split: split_if_asm)
next
  case (Getfield F D)
  with assms show ?thesis
    by(clarsimp simp add: split_beta is_Ref_def split: split_if_asm)(blast intro: addr_loc_type.intros dest: has_visible_field has_field_mono)
next
  case (Invoke M n)
  with assms obtain a vs ta' va T
    where red': "(ta', va, h') \<in> red_external_aggr P t a M vs h"
    and read': "ReadMem ad al v \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
    and wt': "P,h \<turnstile> a\<bullet>M(vs) : T"
    by(auto split: split_if_asm simp add: is_Ref_def)
  from wf red' wt' tconf have "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>"
    by(rule WT_red_external_aggr_imp_red_external)
  with wf show ?thesis using read' by(rule red_external_read_mem_typeable)
qed(auto simp add: split_beta is_Ref_def split: split_if_asm)

lemma exec_1_d_read_typeable:
  "\<lbrakk> wf_prog wf_md P; P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); 
     ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; P,h \<turnstile> t \<surd>t \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,h \<turnstile> ad@al : T'"
apply(erule jvmd_NormalE)
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto intro: exec_instr_read_typeable simp add: check_def)
done

lemma exec_instr_create_object:
  assumes minimal: "heap_ops_typeof_minimal"
  and exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and type: "typeof_addr h' a = \<lfloor>T\<rfloor>" "typeof_addr h a = None"
  shows "\<exists>CTn. NewHeapElem a CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> h' \<turnstile>a a : CTn"
using exec type
proof(cases i)
  case (NewArray T) thus ?thesis using exec type
    apply(auto split: split_if_asm prod.split_asm dest: heap_ops_typeof_minimalD'[OF minimal] new_arr_SomeD)
    apply(frule new_arr_SomeD)
    apply(drule heap_ops_typeof_minimalD'[OF minimal])
    apply(auto split: split_if_asm)
    done
next
  case (Invoke M n) thus ?thesis using exec type
    by(fastsimp dest: red_external_aggr_new_heap_ops_obs[OF minimal] split: prod.split_asm split_if_asm)
qed(auto split: prod.split_asm split_if_asm dest: heap_ops_typeof_minimalD'[OF minimal])

lemma exec_1_create_object:
  assumes minimal: "heap_ops_typeof_minimal"
  shows "\<lbrakk> (ta, xcp', h', frs') \<in> exec P t (xcp, h, frs); typeof_addr h' a = \<lfloor>T\<rfloor>; typeof_addr h a = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> h' \<turnstile>a a : CTn"
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto dest: exec_instr_create_object[OF minimal])
done

lemma exec_1_d_create_object:
  assumes minimal: "heap_ops_typeof_minimal"
  shows "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs');
          typeof_addr h' a = \<lfloor>T\<rfloor>; typeof_addr h a = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> h' \<turnstile>a a : CTn"
by(erule jvmd_NormalE)(rule exec_1_create_object[OF minimal])

lemma JVM_heap_jmm_aux: 
  assumes wf: "wf_prog wf_md P"
  shows "heap_jmm_aux empty_heap new_obj new_arr typeof_addr array_length heap_write
                      JVM_final (mexecd P) (\<tau>MOVE2 P) (\<lambda>t x m. P,m \<turnstile> t \<surd>t) (\<lambda>_ _ _ _. True) P"
apply(unfold_locales)
apply(auto dest: exec_1_d_hext exec_1_d_New_typeof_addrD exec_1_d_New_same_addr_same exec_1_d_create_object exec_1_d_read_typeable[OF wf])
done

lemma JVM_JMM_inst_aux: 
  assumes wf_prog: "wf_prog wf_md P"
  and minimal: "heap_ops_typeof_minimal"
  and start_heap: "start_heap_ok"
  shows "executions_sc (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` 
                        execd_mthr.if.\<E> P (init_fin_lift_state Running (JVM_start_state P C M vs)))
                        P"
proof -
  let ?start_state = "init_fin_lift_state Running (JVM_start_state P C M vs)"
  interpret heap_jmm_aux
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
    JVM_final
    "mexecd P"
    "\<tau>MOVE2 P"
    "\<lambda>t x m. P,m \<turnstile> t \<surd>t"
    "\<lambda>_ _ _ _. True"
    P
    using wf_prog by(rule JVM_heap_jmm_aux)

  note minimal start_heap
  moreover have "ts_inv (init_fin_lift_inv (\<lambda>_ _ _ _. True)) (\<lambda>_. \<lfloor>()\<rfloor>) (thr ?start_state) (shr ?start_state)"
    unfolding ts_inv_init_fin_lift_inv_init_fin_lift_state by(auto intro: ts_invI)
  moreover have "ts_ok (init_fin_lift (\<lambda>t x m. P,m \<turnstile> t \<surd>t)) (thr ?start_state) (shr ?start_state)"
    using start_heap unfolding ts_ok_init_fin_lift_init_fin_lift_state
    by(rule thread_conf_start_state)
  ultimately show ?thesis
    unfolding init_fin_lift_state_start_state by(rule JMM_inst_aux)
qed

end

section {* Locale @{text exeuctions} *}

context JVM_conf_read begin

lemma exec_1_write_typeable:
  assumes wt_prog: "wf_jvm_prog\<^sub>\<Phi> P"
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs)\<surd>"
  and exec: "(ta, xcp', h', frs') \<in> exec P t (xcp, h, frs)"
  and "write": "WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T'. P,h' \<turnstile> ad@al : T' \<and> P,h' \<turnstile> v :\<le> T'"
proof -
  from exec "write" obtain stk loc C M pc FRS 
    where frs: "frs = (stk, loc, C, M, pc) # FRS" 
    and None: "xcp = None"
    and exec_i: "(ta, xcp', h', frs') \<in> exec_instr (instrs_of P C M ! pc) P t h stk loc C M pc FRS"
    by(cases "(P, t, xcp, h, frs)" rule: exec.cases) fastsimp+
  with cs obtain Ts T mxs mxl\<^isub>0 "is" xt ST LT
    where hconf: "hconf h"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl\<^isub>0, is, xt) in C"
    and \<Phi>_pc: "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and ST: "P,h \<turnstile> stk [:\<le>] ST"
    and LT: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT"
    and pc: "pc < length is"
    and tconf: "P,h \<turnstile> t \<surd>t"
    by(auto simp add: defs1) blast

  note [simp del] = split_paired_Ex
  note [simp] = defs1 list_all2_Cons2
  
  from wt_prog obtain wf_md where wf: "wf_prog wf_md P" by(auto dest: wt_jvm_progD)
  from wt_prog sees pc have wt: "P,T,mxs,size is,xt \<turnstile> is!pc,pc :: \<Phi> C M"
    by(rule wt_jvm_prog_impl_wt_instr)

  from exec cs have "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
    by(simp add: welltyped_commute[OF wt_prog] exec_1_iff del: defs1)
  hence hext: "h \<unlhd> h'" by(rule exec_1_d_hext)
  
  from exec_i sees 
  have exec_i: "(ta, xcp', h', frs') \<in> exec_instr (is ! pc) P t h stk loc C M pc FRS" by simp
  with "write" show ?thesis
  proof(cases "is ! pc")
    case AStore [simp]
    from wt \<Phi>_pc have lST: "length ST > 2" by(auto)

    from exec_i "write"
    have stkNN: "hd (tl (tl stk)) \<noteq> Null" by auto
    hence STNN: "hd (tl (tl ST)) \<noteq> NT"       
    proof(rule contrapos_nn)
      assume "hd (tl (tl ST)) = NT"
      moreover
      from ST lST have "P,h \<turnstile> hd (tl (tl stk)) :\<le> hd (tl (tl ST))"
        by (cases ST, auto, case_tac list, auto, case_tac lista, auto)
      ultimately show "hd (tl (tl stk)) = Null" by(simp)
    qed
    with stkNN \<Phi>_pc wt obtain ST'' Y X
      where "ST = Y # Integer # X\<lfloor>\<rceil> # ST''" by(fastsimp)
    with ST obtain ref e idx stk' where stk': "stk = e#idx#ref#stk'" 
      and idx: "P,h \<turnstile> idx :\<le> Integer" and ref:  "P,h \<turnstile> ref :\<le> X\<lfloor>\<rceil>" 
      and e: "P,h \<turnstile> e :\<le> Y" by auto
    from stkNN stk' have "ref \<noteq> Null" by(simp)
    with ref obtain a Xel where a: "ref = Addr a"
      and ha: "typeof_addr h a = \<lfloor>Array Xel\<rfloor>"
      and Xel: "P \<turnstile> Xel \<le> X"
      by(cases ref)(auto simp add: conf_def widen_Array dest: typeof_addr_eq_Some_conv)

    from idx obtain idxI where idxI: "idx = Intg idxI"
      by(auto simp add: conf_def)

    from exec_i "write" stk' `ref \<noteq> Null` idxI a ha
    have "0 <=s idxI" "sint idxI < int (array_length h a)" "P \<turnstile> the (typeof\<^bsub>h\<^esub> e) \<le> Xel"
      and "ad = the_Addr (hd (tl (tl stk)))"
      and "al = ACell (nat (sint (the_Intg (hd (tl stk)))))"
      and "v = e"
      by(auto split: split_if_asm)
    moreover from hext e have "typeof\<^bsub>h'\<^esub> e = typeof\<^bsub>h\<^esub> e" by(auto simp add: conf_def hext_typeof_mono) 
    moreover from hext ha have "typeof_addr h' a = \<lfloor>Array Xel\<rfloor>" by(rule typeof_addr_hext_mono)
    moreover from hext ha have "array_length h' a = array_length h a" by(rule hext_arrD)
    ultimately show ?thesis using stk' idxI a e
      by(fastsimp intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def conf_def)
  next
    case (Putfield F D)[simp]
    from \<Phi>_pc wt obtain vT vT' oT ST'' fm where "ST = vT # oT # ST''" 
      and field: "P \<turnstile> D sees F:vT' (fm) in D"
      and oT: "P \<turnstile> oT \<le> Class D"
      and vT': "P \<turnstile> vT \<le> vT'" by fastsimp
    with ST obtain v' ref stk' where stk': "stk = v'#ref#stk'" 
      and ref:  "P,h \<turnstile> ref :\<le> oT" 
      and v': "P,h \<turnstile> v' :\<le> vT" by auto

    from field wf have DObject: "D \<noteq> Object"
      by(auto dest: wf_Object_field_empty has_fields_fun simp add: sees_field_def)

    from exec_i "write" stk' have "ref \<noteq> Null" by(auto split: split_if_asm)
    from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
    with `ref \<noteq> Null` DObject obtain a D' where 
      a: "ref = Addr a" and h: "typeof_addr h a = Some (Class D')" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
      by (blast dest: non_npD)

    from field D' have has_field: "P \<turnstile> D' has F:vT' (fm) in D"
      by (blast intro: has_field_mono has_visible_field)
    with h have al: "P,h \<turnstile> a@CField D F : vT'" ..
    moreover from v' vT' have "P,h \<turnstile> v' :\<le> vT'" by auto
    moreover from exec_i "write" stk' `ref \<noteq> Null` a
    have "ad = a" "al = CField D F" "v = v'" by(auto)
    ultimately show ?thesis using hext
      by(blast intro: addr_loc_type_hext_mono conf_hext)
  next
    case (Invoke M' n)[simp]

    from wt \<Phi>_pc have n: "n < size ST" by simp
    
    from exec_i "write" have Null: "stk!n \<noteq> Null" by(simp split: split_if_asm)
    hence NT: "ST!n \<noteq> NT"
    proof(rule contrapos_nn)
      assume "ST!n = NT"
      moreover from ST n have "P,h \<turnstile> stk!n :\<le> ST!n" by (simp add: list_all2_conv_all_nth)
      ultimately show "stk!n = Null" by simp
    qed

    from NT wt \<Phi>_pc
    have iec: "if is_external_call P (ST ! n) M' then \<exists>U Ts. P \<turnstile> rev (take n ST) [\<le>] Ts \<and> P \<turnstile> ST ! n\<bullet>M'(Ts) :: U
      else \<exists>D D' Ts T m. ST!n = Class D \<and> P \<turnstile> D sees M': Ts\<rightarrow>T = m in D' \<and> P \<turnstile> rev (take n ST) [\<le>] Ts"
      by(fastsimp split: split_if_asm simp add: split_beta)

    show ?thesis
    proof(cases "is_external_call P (ST ! n) M'")
      case False
      with iec obtain D D' Ts T m
        where D: "ST!n = Class D"
	and m_D: "P \<turnstile> D sees M': Ts\<rightarrow>T = m in D'"
	and Ts:  "P \<turnstile> rev (take n ST) [\<le>] Ts"
        by auto
      from n ST D have "P,h \<turnstile> stk!n :\<le> Class D"
	by (auto simp add: list_all2_conv_all_nth)
      from m_D wf have DObject: "D \<noteq> Object"
	by(auto dest: wf_Object_method_empty simp add: wf_jvm_prog_phi_def)
      from `P,h \<turnstile> stk!n :\<le> Class D` Null DObject 
      obtain a C' where
	Addr:   "stk!n = Addr a" and
	obj:    "typeof_addr h a = Some (Class C')" and
	C'subD: "P \<turnstile> C' \<preceq>\<^sup>* D"
        by(cases "stk ! n")(auto simp add: conf_def widen_Class dest: typeof_addr_eq_Some_conv)
      with Call_lemma[OF m_D C'subD wf] exec_i "write" Null have False
        by(auto split: split_if_asm dest: external_call_not_sees_method)
      thus ?thesis ..
    next
      case True
      then obtain U TS where iec: "is_external_call P (ST ! n) M'"
	and wtext: "P \<turnstile> ST ! n\<bullet>M'(TS) :: U" and sub: "P \<turnstile> rev (take n ST) [\<le>] TS"
        using iec by auto
          
      from n ST have "P,h \<turnstile> stk!n :\<le> ST ! n" by-(rule list_all2_nthD2)
      moreover from iec have "is_refT (ST ! n)" by(rule is_external_call_is_refT)
      ultimately obtain a where a: "stk ! n = Addr a" using Null
	by(cases "stk ! n")(auto simp add: conf_def widen_Class elim!: is_refT.cases)
      with `P,h \<turnstile> stk!n :\<le> ST ! n` obtain Ta ao
	where Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>" "P \<turnstile> Ta \<le> ST ! n" "Ta \<noteq> NT"
	by(auto simp add: conf_def dest: typeof_addr_eq_Some_conv)
      
      from ST have "P,h \<turnstile> take n stk [:\<le>] take n ST" by(rule list_all2_takeI)
      then obtain Us where "map typeof\<^bsub>h\<^esub> (take n stk) = map Some Us" "P \<turnstile> Us [\<le>] take n ST"
	by(auto simp add: confs_conv_map)
      hence Us: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some (rev Us)" "P \<turnstile> rev Us [\<le>] rev (take n ST)"
	by- (simp only: rev_map[symmetric], simp)
      with sub have "P \<turnstile> rev Us [\<le>] TS" by(auto intro: widens_trans)
      show ?thesis
      proof(cases "\<exists>D. Ta = Class D \<and> P \<turnstile> D has M'")
        case True
        with Ta a iec exec_i "write" have False unfolding has_method_def
          by(auto dest: external_call_not_sees_method split: split_if_asm)
        thus ?thesis ..
      next
        case False
        with wtext `P \<turnstile> Ta \<le> ST ! n` `Ta \<noteq> NT` obtain U'
	  where "P \<turnstile> Ta\<bullet>M'(TS) :: U'" "P \<turnstile> U' \<le> U"
	  by(auto dest: external_WT_widen_mono split: ty.splits)
        moreover from `P \<turnstile> Us [\<le>] take n ST` n have "length Us = n" by(auto dest: list_all2_lengthD)
        ultimately have iec': "is_external_call P Ta M'" by-(drule external_WT_is_external_call, simp)
        
        from Ta Us `P \<turnstile> Ta\<bullet>M'(TS) :: U'` `P \<turnstile> Us [\<le>] take n ST` sub
        have wtext: "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : U'"
          by(auto intro!: external_WT'.intros simp add: list_all2_rev1 intro: widens_trans)

        from exec_i "write" a obtain ta' va
          where red_ext: "(ta', va, h') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
          and write': "WriteMem ad al v \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" by(auto split: split_if_asm)
        
        from wf red_ext wtext tconf have "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>"
          by(rule WT_red_external_aggr_imp_red_external)
        with wf show ?thesis using write' hconf by(rule red_external_write_typeable)
      qed
    qed
  qed(auto split: prod.split_asm split_if_asm)
qed

lemma exec_1_d_write_typeable:
  assumes wt_prog: "wf_jvm_prog\<^sub>\<Phi> P"
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs)\<surd>"
  and exec: "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and "write": "WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T'. P,h' \<turnstile> ad@al : T' \<and> P,h' \<turnstile> v :\<le> T'"
using exec
by(rule jvmd_NormalE)(rule exec_1_write_typeable[OF wt_prog cs _ "write"])

lemma JVM_heap_jmm:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  shows "heap_jmm empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf
                  JVM_final (mexecd P) (\<tau>MOVE2 P) (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>) (\<lambda>_ _ _ _. True) P"
proof -
  from wf obtain wfmd where "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
  hence "heap_jmm_aux empty_heap new_obj new_arr typeof_addr array_length heap_write JVM_final (mexecd P) (\<tau>MOVE2 P) (\<lambda>t x m. P,m \<turnstile> t \<surd>t) (\<lambda>_ _ _ _. True) P"
    by(rule JVM_heap_jmm_aux)
  moreover {
    interpret lifting_wf JVM_final "mexecd P" convert_RA "\<lambda>t (xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
      using wf by(rule lifting_wf_correct_state_d)
    have "lifting_inv (mexecd P) (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) (\<lambda>_ _ _ _. True)"
      by(unfold_locales) auto }
  ultimately
  interpret heap_jmm_aux empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
                       JVM_final "mexecd P" "\<tau>MOVE2 P" "\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>" "\<lambda>_ _ _ _. True" P
    by(rule heap_jmm_aux.heap_jmm_aux_wfix_mono)(simp add: correct_state_def split_beta)

  show ?thesis
    by(unfold_locales)(auto dest: exec_1_d_NewArr_lengthD exec_1_d_write_typeable[OF wf])
qed

end

interpretation jmm'!: JVM_typesafe 
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

notation jmm'.correct_state ("_,_ \<turnstile>jmm' _:_ \<surd>"  [61,0,0,0] 61)

abbreviation jmm'_exec_instr :: 
  "instr \<Rightarrow> jvm_prog \<Rightarrow> thread_id \<Rightarrow> JMM_heap \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> frame list
   \<Rightarrow> (JMM_heap jvm_thread_action \<times> JMM_heap jvm_state) set"
where "jmm'_exec_instr i P \<equiv> jmm'.exec_instr P i P"

abbreviation jmm'_exec_1_d :: 
  "jvm_prog \<Rightarrow> thread_id \<Rightarrow> JMM_heap jvm_state type_error \<Rightarrow> JMM_heap jvm_thread_action 
  \<Rightarrow> JMM_heap jvm_state type_error \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' _ -_-jvmd\<rightarrow> _" [61,0,61,0,61] 60)
where "jmm'_exec_1_d P \<equiv> jmm'.exec_1_d P P"


declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

lemma exec_instr_cut_and_update:
  assumes wf: "wf_prog wf_md P"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile>jmm' ad@al : T \<and> P,shr s \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,shr s \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and hconf: "P \<turnstile>jmm' shr s \<surd>"
  and tconf: "P,shr s \<turnstile>jmm' t \<surd>t"
  and exec_i: "(ta, xcp', h', frs') \<in> jmm'_exec_instr i P t (shr s) stk loc C M pc frs"
  and check: "jmm'.check_instr i P (shr s) stk loc C M pc frs"
  and aok: "jmm'.execd_mthr.if.actions_ok s t ta"
  shows "\<exists>ta' xcp'' h'' frs''. (ta', xcp'', h'', frs'') \<in> jmm'_exec_instr i P t (shr s) stk loc C M pc frs \<and>
           jmm'.execd_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
using exec_i aok
proof(cases i)
  case MExit thus ?thesis using exec_i aok
    by(simp add: split_beta split: split_if_asm)(safe, fastsimp, fastsimp intro!: disjI2 del: disjCI)
next
  case ALoad[simp]
  let ?a = "the_Addr (hd (tl stk))"
  let ?i = "the_Intg (hd stk)"
  show ?thesis
  proof(cases "hd (tl stk) = Null \<or> ?i <s 0 \<or> int (jmm_array_length (shr s) ?a) \<le> sint ?i")
    case True
    with exec_i aok show ?thesis by(auto split: split_if_asm)
  next
    case False
    hence Null: "hd (tl stk) \<noteq> Null"
      and bounds: "0 <=s ?i" "sint ?i < int (jmm_array_length (shr s) ?a)" by auto
    from Null check obtain T 
      where type: "jmm_typeof_addr (shr s) ?a = \<lfloor>Array T\<rfloor>" by auto
    from bounds have "nat (sint ?i) < jmm_array_length (shr s) ?a"
      by(simp add: word_sle_def nat_less_iff)
    with type have adal: "P,shr s \<turnstile>jmm' ?a@ACell (nat (sint ?i)) : T"
      by(rule jmm'.addr_loc_type.intros)
    then obtain b v' where bv': "vs (?a, ACell (nat (sint ?i))) = \<lfloor>(v', b)\<rfloor>"
      using subsetD[OF dom_vs, where c="(?a, ACell (nat (sint ?i)))"] by fastsimp
    with adal have "P,shr s \<turnstile>jmm' v' :\<le> T" by(auto dest: vs jmm'.addr_loc_type_fun)
    with adal have "jmm_heap_read' P (shr s) ?a (ACell (nat (sint ?i))) v'"
      by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
    with bv' type bounds Null aok exec_i show ?thesis by fastsimp
  qed
next
  case (Getfield F D)[simp]
  let ?a = "the_Addr (hd stk)"
  show ?thesis
  proof(cases "hd stk = Null")
    case True
    with exec_i aok show ?thesis by(auto)
  next
    case False
    with check obtain T fm C
      where sees: "P \<turnstile> D sees F:T (fm) in D"
      and type: "jmm_typeof_addr (shr s) ?a = \<lfloor>Class C\<rfloor>"
      and sub: "P \<turnstile> C \<preceq>\<^sup>* D" by auto
    from has_visible_field[OF sees] sub
    have "P \<turnstile> C has F:T (fm) in D" by(rule has_field_mono)
    with type have adal: "P,shr s \<turnstile>jmm' ?a@CField D F : T"
      by(rule jmm'.addr_loc_type.intros)
    then obtain b v' where bv': "vs (?a, CField D F) = \<lfloor>(v', b)\<rfloor>"
      using subsetD[OF dom_vs, where c="(?a, CField D F)"] by fastsimp
    with adal have "P,shr s \<turnstile>jmm' v' :\<le> T" by(auto dest: vs jmm'.addr_loc_type_fun)
    with adal have "jmm_heap_read' P (shr s) ?a (CField D F) v'"
      by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
    with bv' aok False exec_i show ?thesis by(auto)
  qed
next
  case (Invoke M n)[simp]
  let ?a = "the_Addr (stk ! n)"
  let ?vs = "rev (take n stk)"
  show ?thesis
  proof(cases "stk ! n = Null \<or> \<not> is_external_call P (the (jmm_typeof_addr (shr s) ?a)) M")
    case True with exec_i aok show ?thesis by auto
  next
    case False
    hence Null: "stk ! n \<noteq> Null" 
      and iec: "is_external_call P (the (jmm_typeof_addr (shr s) ?a)) M" by simp_all
    with check obtain T U
      where type: "jmm_typeof_addr (shr s) ?a = \<lfloor>T\<rfloor>"
      and extwt: "P,shr s \<turnstile>jmm' ?a\<bullet>M(?vs) : U" by auto
    from Null iec type exec_i obtain ta' va
      where red: "(ta', va, h') \<in> jmm'_red_external_aggr P t ?a M ?vs (shr s)"
      and ta: "ta = extTA2JVM P ta'" by(fastsimp)
    from wf red extwt tconf have red': "P,t \<turnstile>jmm' \<langle>?a\<bullet>M(?vs),shr s\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>"
      by(rule jmm'.WT_red_external_aggr_imp_red_external)
    from aok ta have "jmm'.execd_mthr.if.actions_ok s t ta'" by simp
    from jmm'.execd_mthr.if.red_external_cut_and_update[OF wf vs dom_vs red' this hconf, of "\<lambda>_ _ _ b. b"]
    obtain ta'' va'' h'' where "P,t \<turnstile>jmm' \<langle>the_Addr (stk ! n)\<bullet>M(rev (take n stk)), shr s\<rangle> -ta''\<rightarrow>ext \<langle>va'',h''\<rangle>"
      and "jmm'.execd_mthr.if.actions_ok s t ta''"
      and "ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
      and "eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) vs"
      by blast
    thus ?thesis using Null iec ta
      by(cases va'')(force dest!: jmm'.red_external_imp_red_external_aggr)+
  qed
qed(auto simp add: split_beta split: split_if_asm)

lemma exec_1_d_cut_and_update:
  assumes "wf_prog wf_md P"
  and "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile>jmm' ad@al : T \<and> P,shr s \<turnstile>jmm' v :\<le> T"
  and "{(ad, al). \<exists>T. P,shr s \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and "P \<turnstile>jmm' shr s \<surd>"
  and "P,shr s \<turnstile>jmm' t \<surd>t"
  and "P,t \<turnstile>jmm' Normal (xcp, shr s, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and "jmm'.execd_mthr.if.actions_ok s t ta"
  shows "\<exists>ta' xcp'' h'' frs''. P,t \<turnstile>jmm' Normal (xcp, shr s, frs) -ta'-jvmd\<rightarrow> Normal (xcp'', h'', frs'') \<and>
           jmm'.execd_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
using assms
apply -
apply(erule jmm'.jvmd_NormalE)
apply(cases "(P, t, xcp, shr s, frs)" rule: jmm'.exec.cases)
  apply simp
 prefer 2
 apply(fastsimp simp add: jmm'.exec_1_d.simps jmm'.exec_d_def split_beta)
apply clarsimp
apply(drule exec_instr_cut_and_update, assumption+)
  apply(clarsimp simp add: jmm'.check_def has_method_def)
 apply simp
apply(fastsimp simp add: jmm'.exec_1_d.simps jmm'.exec_d_def)
done

declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

lemma JVM_cut_and_update:
  assumes wf_prog: "wf_jvm_prog\<^sub>\<Phi> P"
  and start_heap: "jmm'.start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,jmm'.start_heap \<turnstile>jmm' vs [:\<le>] Ts"
  shows "jmm'.execd_mthr_if.cut_and_update P (init_fin_lift_state Running (jmm'.JVM_start_state P C M vs)) 
                                           (mrw_values P empty (map snd (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)))"
  (is "jmm'.execd_mthr_if.cut_and_update _ ?start_state ?start_vs")
proof(rule jmm'.execd_mthr_if.cut_and_updateI)
  fix ttas s' t x ta x' m'
  assume \<tau>Red: "jmm'.execd_mthr.if.mthr.\<tau>rtrancl3p P P ?start_state ttas s'"
    and sc: "ta_seq_consist P ?start_vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and ts't: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "jmm'.execd_mthr.init_fin P P t (x, shr s') ta (x', m')"
    and aok: "jmm'.execd_mthr.if.actions_ok s' t ta"
    and n\<tau>: "\<not> jmm'.execd_mthr.init_fin_\<tau>move P (x, shr s') ta (x', m')"

  let ?conv = "\<lambda>ttas. concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)"
  let ?vs' = "mrw_values P ?start_vs (?conv ttas)"
  let ?wfix = "init_fin_lift_inv (\<lambda>_ _ _ _. True)"
  let ?wfx = "init_fin_lift (\<lambda>t (xcp, frstls) h. P,\<Phi> \<turnstile>jmm' t: (xcp, h, frstls) \<surd>)"
  let ?start_obs = "map snd (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)"

  interpret heap_jmm
    jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm_heap_read' P" "jmm_heap_write' P" "jmm_hconf P"
    JVM_final
    "jmm'.mexecd P P"
    "jmm'.\<tau>MOVE2 P"
    "\<lambda>t (xcp, frstls) h. P,\<Phi> \<turnstile>jmm' t: (xcp, h, frstls) \<surd>" 
    "\<lambda>_ _ _ _. True" 
    P
    using wf_prog by(rule jmm'.JVM_heap_jmm)

  from wf_prog obtain wf_md where wf: "wf_prog wf_md P" by(auto dest: wt_jvm_progD)

  from wf_prog start_heap sees conf
  have "jmm'.correct_jvm_state P \<Phi> (jmm'.JVM_start_state P C M vs)"
    by(rule jmm'.correct_jvm_state_initial)
  hence wfx: "ts_ok ?wfx (thr ?start_state) (shr ?start_state)"
    unfolding ts_ok_init_fin_lift_init_fin_lift_state
    by(simp add: jmm'.correct_jvm_state_def)

  have wfix: "ts_inv ?wfix (\<lambda>_. \<lfloor>()\<rfloor>) (thr ?start_state) (shr ?start_state)" by(auto intro: ts_invI)

  from \<tau>Red wfx have wfx': "ts_ok ?wfx (thr s') (shr s')"
    by(rule wfix_if.redT_\<tau>rtrancl3p_preserves)

  from \<tau>Red have hext: "shr ?start_state \<unlhd>jmm' shr s'"
    by(rule init_fin_\<tau>rtrancl3p_hext)

  show "\<exists>ta' x'' m''. jmm'.execd_mthr.init_fin P P t (x, shr s') ta' (x'', m'') \<and>
                      jmm'.execd_mthr.if.actions_ok s' t ta' \<and>
                      \<not> jmm'.execd_mthr.init_fin_\<tau>move P (x, shr s') ta' (x'', m'') \<and>
                      ta_seq_consist P ?vs' (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                      eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs'"
  proof(cases "ta_seq_consist P ?vs' (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)")
    case True
    hence "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ?vs'"
      by(rule ta_seq_consist_imp_eq_upto_seq_inconsist_refl)
    with red aok n\<tau> True show ?thesis by blast
  next
    case False
    with red obtain xcp frs xcp' frs' ta'
      where x: "x = (Running, xcp, frs)" and x': "x' = (Running, xcp', frs')"
      and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
      and red': "P,t \<turnstile>jmm' Normal (xcp, shr s', frs) -ta'-jvmd\<rightarrow> Normal (xcp', m', frs')"
      by cases fastsimp+

    from ts't x wfx' have cs: "P,\<Phi> \<turnstile>jmm' t:(xcp, shr s', frs) \<surd>" by(auto dest: ts_okD)
    hence hconf: "P \<turnstile>jmm' shr s' \<surd>"
      and tconf: "P,shr s' \<turnstile>jmm' t \<surd>t" by(simp_all add: jmm'.correct_state_def) 
    
    have aok': "jmm'.execd_mthr.if.actions_ok s' t ta'"
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
        using \<tau>Red wfx wfix by-(rule \<tau>RedT_mrw_values_typeable) }
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

    from exec_1_d_cut_and_update[OF wf wt_vs this hconf tconf red' aok', where ?b3="\<lambda>_ _ _ b. b"] 
    obtain ta'' xcp'' h'' frs''
      where red'': "P,t \<turnstile>jmm' Normal (xcp, shr s', frs) -ta''-jvmd\<rightarrow> Normal (xcp'', h'', frs'')"
      and aok'': "jmm'.execd_mthr.if.actions_ok s' t ta''"
      and sc'': "ta_seq_consist P ?vs' (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
      and eq'': "eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) ?vs'"
      by blast

    from n\<tau> x x' have "\<not> jmm'.\<tau>Move2 P (xcp, shr s', frs) \<or> ta \<noteq> \<epsilon>"
      by(auto intro: jmm'.execd_mthr.init_fin_\<tau>move.intros)
    with red x x' have "\<not> jmm'.\<tau>Move2 P (xcp, shr s', frs)"
      by(auto dest: jmm'.\<tau>exec_1_taD)
    hence n\<tau>'': "\<not> jmm'.\<tau>MOVE2 P ((xcp, frs), shr s') ta'' ((xcp'', frs''), h'')" by auto

    let ?x' = "(Running, xcp'', frs'')"
    let ?ta' = "convert_TA_initial (convert_obs_initial ta'')"
    from red'' have "jmm'.execd_mthr.init_fin P P t (x, shr s') ?ta' (?x', h'')"
      unfolding x by -(rule jmm'.execd_mthr.init_fin.NormalAction, simp)
    moreover from aok'' have "jmm'.execd_mthr.if.actions_ok s' t ?ta'" by simp
    moreover from n\<tau>'' have "\<not> jmm'.execd_mthr.init_fin_\<tau>move P (x, shr s') ?ta' (?x', h'')"
      unfolding x by auto
    moreover from sc'' have "ta_seq_consist P ?vs' (llist_of \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub>)" by simp
    moreover from eq'' have "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> ?vs'" unfolding ta by simp
    ultimately show ?thesis by blast
  qed
qed

theorem JVM_JMM_inst: 
  assumes wf_prog: "wf_jvm_prog\<^sub>\<Phi> P"
  and minimal: "jmm'_heap_ops_typeof_minimal P"
  and start_heap: "jmm'.start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,jmm'.start_heap \<turnstile>jmm' vs [:\<le>] Ts"
  shows "executions (lappend (llist_of (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)) ` 
                     jmm'.execd_mthr.if.\<E> P P (init_fin_lift_state Running (jmm'.JVM_start_state P C M vs)))
                    P"
  (is "executions ?E _")
proof -
  let ?start_state = "init_fin_lift_state Running (jmm'.JVM_start_state P C M vs)"

  interpret heap_jmm
    jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm_heap_read' P" "jmm_heap_write' P" "jmm_hconf P"
    JVM_final
    "jmm'.mexecd P P"
    "jmm'.\<tau>MOVE2 P"
    "\<lambda>t (xcp, frstls) h. P,\<Phi> \<turnstile>jmm' t: (xcp, h, frstls) \<surd>" 
    "\<lambda>_ _ _ _. True" 
    P
    using wf_prog by(rule jmm'.JVM_heap_jmm)

  from wf_prog obtain wf_md where "wf_prog wf_md P" by(auto dest: wt_jvm_progD)
  then interpret JVM_jmm!: executions_sc ?E P
    using minimal start_heap by(rule jmm'.JVM_JMM_inst_aux)

  interpret Jinja_executions_aux
    JVM_final
    "jmm'.mexecd P P"
    "jmm'.\<tau>MOVE2 P"
    "jmm'.start_heap_obs"
    "jmm'.start_tid"
    "?start_state" 
    P
    by unfold_locales(auto simp add: jmm'.start_heap_obs_not_Read jmm'.start_state_def init_fin_lift_state_def split_beta split: split_if_asm intro!: Status_no_wait_locksI)

  from wf_prog start_heap sees conf
  show ?thesis
    by(rule executions[unfolded start_heap_obs_def, OF JVM_cut_and_update])
qed

end