(*  Title:      JinjaThreads/BV/JVMDeadlocked.thy
    Author:     Andreas Lochbihler
*)
header{* \isaheader{Progress result for both of the multithreaded JVMs} *}

theory BVProgressThreaded
imports
  "../Framework/FWProgress"
  "../Framework/FWLiftingSem"
  BVNoTypeError
  "../JVM/JVMThreaded"
begin

lemma (in JVM_heap_base) mexec_final_wf: "final_thread_wf JVM_final (mexec P)"
proof(unfold_locales)
  fix x t m ta x' m'
  assume "JVM_final x" "mexec P t (x, m) ta (x', m')"
  moreover obtain xcp frs tls where x: "x = (xcp, frs)" by (cases x, auto)
  ultimately have "frs = []" by simp
  moreover have "\<not> P,t \<turnstile> (xcp, m, []) -ta-jvm\<rightarrow> (fst x', m', snd x')"
    by(simp add: exec_1_iff)
  ultimately show False using `mexec P t (x, m) ta (x', m')` x by(auto)
qed

sublocale JVM_heap_base < exec_mthr!: final_thread_wf
  JVM_final
  "mexec P"
  convert_RA
  for P
by(rule mexec_final_wf)

lemma (in JVM_heap_base) mexecd_final_wf: "final_thread_wf JVM_final (mexecd P)"
proof(unfold_locales)
  fix x t m ta x' m'
  assume "JVM_final x" "mexecd P t (x, m) ta (x', m')"
  moreover obtain xcp frs where x: "x = (xcp, frs)" by (cases x, auto)
  ultimately have "frs = []" by simp
  moreover have "\<not> P,t \<turnstile> Normal (xcp, m, []) -ta-jvmd\<rightarrow> Normal (fst x', m', snd x')"
    by(auto elim!: exec_1_d.cases simp add: exec_d_def split: split_if_asm)
  ultimately show False using `mexecd P t (x, m) ta (x', m')` x by(auto)
qed

sublocale JVM_heap_base < execd_mthr!: final_thread_wf 
  JVM_final
  "mexecd P"
  convert_RA
  for P
by(rule mexecd_final_wf)

lemma (in JVM_heap_conf_base') mexec_eq_mexecd:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; \<Phi> \<turnstile> t: (xcp, h, frs) \<surd> \<rbrakk> \<Longrightarrow> mexec P t ((xcp, frs), h) = mexecd P t ((xcp, frs), h)"
apply(auto intro!: ext)
 apply(unfold exec_1_iff)
 apply(drule no_type_error)
  apply(assumption)
 apply(clarify)
 apply(rule exec_1_d_NormalI)
  apply(assumption)
 apply(simp add: exec_d_def split: split_if_asm)
apply(erule jvmd_NormalE, auto)
done

(* conformance lifted to multithreaded case *)

context JVM_heap_conf_base begin

abbreviation 
  correct_state_ts :: "ty\<^isub>P \<Rightarrow> (addr,thread_id,jvm_thread_state) thread_info \<Rightarrow> 'heap \<Rightarrow> bool"
where
  "correct_state_ts \<Phi> \<equiv> ts_ok (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>)"

lemma invoke_new_thread:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl0,ins,xt) in C"
  and "ins ! pc = Invoke Type.start 0"
  and "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  and "\<Phi> \<turnstile> t: (None, h, (stk, loc, C, M, pc) # frs) \<surd>"
  and "typeof_addr h a = \<lfloor>Class D\<rfloor>"
  and "P \<turnstile> D \<preceq>\<^sup>* Thread"
  and "P \<turnstile> D sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'"
  shows "\<Phi> \<turnstile> a: (None, h, [([], Addr a # replicate mxl0' undefined, D', run, 0)]) \<surd>"
proof -
  from `\<Phi> \<turnstile> t: (None, h, (stk, loc, C, M, pc) # frs) \<surd>`
  have "hconf h" and "preallocated h" by(simp_all add: correct_state_def)
  moreover
  from `P \<turnstile> D sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'`
  have "P \<turnstile> D' sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'"
    by(rule sees_method_idemp)
  with `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P`
  have "wt_start P D' [] mxl0' (\<Phi> D' run)" and "ins' \<noteq> []"
    by(auto dest: wt_jvm_prog_impl_wt_start)
  then obtain LT' where LT': "\<Phi> D' run ! 0 = Some ([], LT')"
    by (clarsimp simp add: wt_start_def defs1 sup_state_opt_any_Some)
  moreover
  have "conf_f P h ([], LT') ins' ([], Addr a # replicate mxl0' undefined, D', run, 0)"
  proof -
    let ?LT = "OK (Class D') # (replicate mxl0' Err)"
    have "P,h \<turnstile> replicate mxl0' undefined [:\<le>\<^sub>\<top>] replicate mxl0' Err" by simp
    also from `P \<turnstile> D sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'`
    have "P \<turnstile> D \<preceq>\<^sup>* D'" by(rule sees_method_decl_above)
    with `typeof_addr h a = \<lfloor>Class D\<rfloor>` have "P,h \<turnstile> Addr a :\<le> Class D'"
      by(simp add: conf_def)
    ultimately have "P,h \<turnstile> Addr a # replicate mxl0' undefined [:\<le>\<^sub>\<top>] ?LT" by(simp)
    also from `wt_start P D' [] mxl0' (\<Phi> D' run)` LT'
    have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT'" by(simp add: wt_start_def)
    finally have "P,h \<turnstile> Addr a # replicate mxl0' undefined [:\<le>\<^sub>\<top>] LT'" .
    with `ins' \<noteq> []` show ?thesis by(simp add: conf_f_def)
  qed
  moreover from `typeof_addr h a = \<lfloor>Class D\<rfloor>` `P \<turnstile> D \<preceq>\<^sup>* Thread` have "P,h \<turnstile> a \<surd>t" by(rule tconfI)
  ultimately show ?thesis using `P \<turnstile> D' sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'`
    by(fastsimp simp add: correct_state_def)
qed

lemma exec_new_threadE:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and "P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and "\<Phi> \<turnstile> t: \<sigma> \<surd>"
  and "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []"
  obtains h frs a stk loc C M pc Ts T mxs mxl0 ins xt M' n Ta ta' va  Us Us' U m'
  where "\<sigma> = (None, h, (stk, loc, C, M, pc) # frs)"
  and "(ta, \<sigma>') \<in> exec P t (None, h, (stk, loc, C, M, pc) # frs)"
  and "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
  and "stk ! n = Addr a"
  and "ins ! pc = Invoke M' n"
  and "n < length stk"
  and "typeof_addr h a = \<lfloor>Ta\<rfloor>"
  and "is_external_call P Ta M'"
  and "ta = extTA2JVM P ta'"
  and "\<sigma>' = extRet2JVM n m' stk loc C M pc frs va"
  and "(ta', va, m') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
  and "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us"
  and "P \<turnstile> Ta\<bullet>M'(Us') :: U"
  and "P \<turnstile> Us [\<le>] Us'"
proof -
  from `P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'` obtain h f Frs xcp
    where check: "check P \<sigma>"
    and exec: "(ta, \<sigma>') \<in> exec P t \<sigma>"
    and [simp]: "\<sigma> = (xcp, h, f # Frs)"
    by(rule jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)"
    by(cases f, blast)
  from `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` exec have [simp]: "xcp = None" by(cases xcp) auto
  from `\<Phi> \<turnstile> t: \<sigma> \<surd>`
  obtain Ts T mxs mxl0 ins xt ST LT 
    where "hconf h" "preallocated h"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastsimp simp add: correct_state_def)
  from check `\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>` sees
  have checkins: "check_instr (ins ! pc) P h stk loc C M pc Frs"
    by(clarsimp simp add: check_def)
  from sees `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` exec obtain M' n where [simp]: "ins ! pc = Invoke M' n"
    by(cases "ins ! pc", auto split: split_if_asm simp add: split_beta ta_upd_simps)
  from `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P` obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
  
  from checkins have "n < length stk" "is_Ref (stk ! n)" by auto
  moreover from exec sees `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` have "stk ! n \<noteq> Null" by auto
  with `is_Ref (stk ! n)` obtain a where "stk ! n = Addr a"
    by(auto simp add: is_Ref_def elim: is_AddrE)
  moreover with checkins obtain Ta where Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>" by(fastsimp)
  moreover with checkins exec sees `n < length stk` `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` `stk ! n = Addr a`
  obtain Us Us' U where "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us"
    and "P \<turnstile> Ta\<bullet>M'(Us') :: U" "is_external_call P Ta M'" "P \<turnstile> Us [\<le>] Us'"
    by(auto simp add: min_def split_beta has_method_def external_WT'_iff split: split_if_asm dest: external_call_not_sees_method)
  moreover with `typeof_addr h a = \<lfloor>Ta\<rfloor>` `n < length stk` exec sees `stk ! n = Addr a`
  obtain ta' va h' where "ta = extTA2JVM P ta'" "\<sigma>' = extRet2JVM n h' stk loc C M pc Frs va"
    "(ta', va, h') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
    by(fastsimp simp add: min_def)
  ultimately show thesis using exec sees by-(rule that, auto)
qed

end

context JVM_conf_read begin

lemma correct_state_new_thread:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and red: "P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and cs: "\<Phi> \<turnstile> t: \<sigma> \<surd>"
  and nt: "NewThread t'' (xcp, frs) h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "\<Phi> \<turnstile> t'': (xcp, h'', frs) \<surd>"
proof -
  from wf obtain wt where wfp: "wf_prog wt P" by(blast dest: wt_jvm_progD)
  from nt have "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []" by auto
  with wf red cs
  obtain h Frs a stk loc C M pc Ts T mxs mxl0 ins xt M' n Ta ta' va h' Us Us' U
    where [simp]: "\<sigma> = (None, h, (stk, loc, C, M, pc) # Frs)"
    and exec: "(ta, \<sigma>') \<in> exec P t (None, h, (stk, loc, C, M, pc) # Frs)"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and [simp]: "stk ! n = Addr a"
    and [simp]: "ins ! pc = Invoke M' n"
    and n: "n < length stk"
    and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
    and iec: "is_external_call P Ta M'"
    and ta: "ta = extTA2JVM P ta'"
    and \<sigma>': "\<sigma>' = extRet2JVM n h' stk loc C M pc Frs va"
    and rel: "(ta', va, h') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
    and Us: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us"
    and wtext: "P \<turnstile> Ta\<bullet>M'(Us') :: U"
    and sub: "P \<turnstile> Us [\<le>] Us'"
    by(rule exec_new_threadE)
  from cs have hconf: "hconf h" and preh: "preallocated h"
    and tconf: "P,h \<turnstile> t \<surd>t" by(auto simp add: correct_state_def)
  from Ta Us wtext sub have wtext': "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : U" by(rule external_WT'.intros)
  from rel have red: "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>"
    by(unfold WT_red_external_list_conv[OF wfp wtext' tconf])
  from ta nt obtain D M'' a' where nt': "NewThread t'' (D, M'', a') h'' \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>"
    "(xcp, frs) = extNTA2JVM P (D, M'', a')" by auto
  with red have [simp]: "h'' = h'" by-(rule red_ext_new_thread_heap)
  from red_external_new_thread_sub_thread[OF red nt'(1)]
  have h't'': "typeof_addr h' a' = \<lfloor>Class D\<rfloor>" "P \<turnstile> D \<preceq>\<^sup>* Thread" and [simp]: "M'' = run" by auto
  from red_external_new_thread_exists_thread_object[OF red nt'(1)] 
  have tconf': "P,h' \<turnstile> t'' \<surd>t" by(auto intro: tconfI)
  from sub_Thread_sees_run[OF wfp `P \<turnstile> D \<preceq>\<^sup>* Thread`] obtain mxs' mxl0' ins' xt' D'
    where seesrun: "P \<turnstile> D sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'" by auto
  with nt' ta nt have "xcp = None" "frs = [([],Addr a' # replicate mxl0' undefined,D',run,0)]"
    by(auto simp add: extNTA2JVM_def split_beta)
  moreover
  have "\<Phi> \<turnstile> t'': (None, h', [([], Addr a' # replicate mxl0' undefined, D', run, 0)]) \<surd>"
  proof -
    from wfp red wtext' `hconf h` have "hconf h'" 
      by(rule external_call_hconf)
    moreover from red have "h \<unlhd> h'" by(rule red_external_hext)
    with preh have "preallocated h'" by(rule preallocated_hext)
    moreover from seesrun
    have seesrun': "P \<turnstile> D' sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'"
      by(rule sees_method_idemp)
    moreover with `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P`
    obtain "wt_start P D' [] mxl0' (\<Phi> D' run)" "ins' \<noteq> []"
      by (auto dest: wt_jvm_prog_impl_wt_start)    
    then obtain LT' where "\<Phi> D' run ! 0 = Some ([], LT')"
      by (clarsimp simp add: wt_start_def defs1 sup_state_opt_any_Some)
    moreover
    have "conf_f P h' ([], LT') ins' ([], Addr a' # replicate mxl0' undefined, D', run, 0)"
    proof -
      let ?LT = "OK (Class D') # (replicate mxl0' Err)"
      from seesrun have "P \<turnstile> D \<preceq>\<^sup>* D'" by(rule sees_method_decl_above)
      hence "P,h' \<turnstile> Addr a' # replicate mxl0' undefined [:\<le>\<^sub>\<top>] ?LT"
	using h't'' by(simp add: conf_def)
      also from `wt_start P D' [] mxl0' (\<Phi> D' run)` `\<Phi> D' run ! 0 = Some ([], LT')`
      have "P \<turnstile> ?LT [\<le>\<^sub>\<top>] LT'" by(simp add: wt_start_def)
      finally have "P,h' \<turnstile> Addr a' # replicate mxl0' undefined [:\<le>\<^sub>\<top>] LT'" .
      with `ins' \<noteq> []` show ?thesis by(simp add: conf_f_def)
    qed
    ultimately show ?thesis using tconf' by(fastsimp simp add: correct_state_def)
  qed
  ultimately show ?thesis by(clarsimp)
qed

lemma correct_state_heap_change:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and red: "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
  and cs'': "\<Phi> \<turnstile> t'': (xcp'', h, frs'') \<surd>"
  shows "\<Phi> \<turnstile> t'': (xcp'', h', frs'') \<surd>"
proof(cases xcp)
  case None
  from cs have "P,h \<turnstile> t \<surd>t" by(simp add: correct_state_def)
  with red have "hext h h'" by (auto intro: exec_1_d_hext simp add: tconf_def)
  from `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P` cs red have "\<Phi> \<turnstile> t: (xcp', h', frs') \<surd>"
    by(auto elim!: jvmd_NormalE intro: BV_correct_1 simp add: exec_1_iff)
  from cs'' have "P,h \<turnstile> t'' \<surd>t" by(simp add: correct_state_def)
  with `h \<unlhd> h'` have tconf': "P,h' \<turnstile> t'' \<surd>t" by-(rule tconf_hext_mono)

  from `\<Phi> \<turnstile> t: (xcp', h', frs') \<surd>`
  have hconf': "hconf h'" "preallocated h'" by(simp_all add: correct_state_def)

  show ?thesis
  proof(cases frs'')
    case Nil thus ?thesis using tconf' hconf' by(simp add: correct_state_def)
  next
    case (Cons f'' Frs'')
    obtain stk'' loc'' C0'' M0'' pc''
      where "f'' = (stk'', loc'', C0'', M0'', pc'')"
      by(cases f'', blast)
    with `frs'' = f'' # Frs''` cs''
    obtain Ts'' T'' mxs'' mxl\<^isub>0'' ins'' xt'' ST'' LT'' 
      where "hconf h"
      and sees'': "P \<turnstile> C0'' sees M0'': Ts''\<rightarrow>T'' = (mxs'', mxl\<^isub>0'', ins'', xt'') in C0''"
      and "\<Phi> C0'' M0'' ! pc'' = \<lfloor>(ST'', LT'')\<rfloor>"
      and "conf_f P h (ST'', LT'') ins'' (stk'', loc'', C0'', M0'', pc'')"
      and "conf_fs P h \<Phi> M0'' (length Ts'') T'' Frs''"
      by(fastsimp simp add: correct_state_def)
    
    show ?thesis using Cons `\<Phi> \<turnstile> t'': (xcp'', h, frs'') \<surd>` `hext h h'` hconf' tconf'
      apply(cases xcp'')
      apply(auto simp add: correct_state_def)
      apply(blast dest: hext_objD intro: conf_fs_hext conf_f_hext)+
      done
  qed
next
  case (Some a)
  with `P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')` have "h = h'" by(auto elim!: jvmd_NormalE)
  with `\<Phi> \<turnstile> t'': (xcp'', h, frs'') \<surd>` show ?thesis by simp
qed

lemma lifting_wf_correct_state_d: "wf_jvm_prog\<^sub>\<Phi> P \<Longrightarrow> lifting_wf (mexecd P) (\<lambda>t (xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>)"
apply(unfold_locales)
by(auto intro: BV_correct_d_1 correct_state_new_thread correct_state_heap_change)

lemma lifting_wf_correct_state:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  shows "lifting_wf (mexec P) (\<lambda>t (xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>)"
proof(unfold_locales)
  fix t x m ta x' m'
  assume "mexec P t (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>) x m"
  with wf show "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>) x' m'"
    by(cases x)(cases x', simp add: welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`], rule BV_correct_d_1)
next
  fix t x m ta x' m' t'' x''
  assume "mexec P t (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>) x m"
    and "NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  with wf show "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t'': (xcp, h, frs) \<surd>) x'' m'"
    apply(cases x, cases x', cases x'', clarify, unfold welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`])
    by(rule correct_state_new_thread)
next
  fix t x m ta x' m' t'' x''
  assume "mexec P t (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>) x m"
    and "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t'': (xcp, h, frs) \<surd>) x'' m"
  with wf show "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t'': (xcp, h, frs) \<surd>) x'' m'"
    apply(cases x, cases x', cases x'', clarify, unfold welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`])
    by(rule correct_state_heap_change)
qed

declare split_paired_Ex [simp del]

lemmas preserves_correct_state = FWLiftingSem.lifting_wf.RedT_preserves[OF lifting_wf_correct_state]
lemmas preserves_correct_state_d = FWLiftingSem.lifting_wf.RedT_preserves[OF lifting_wf_correct_state_d]

end

context JVM_heap_conf_base begin 

lemma execd_NewThread_Thread_Object:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and conf: "\<Phi> \<turnstile> t': \<sigma> \<surd>"
  and red: "P,t' \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and nt: "NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "\<exists>C. typeof_addr (fst (snd \<sigma>')) t = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> Class C \<le> Class Thread"
proof -
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(blast dest: wt_jvm_progD)
  from red obtain h f Frs xcp
    where check: "check P \<sigma>" 
    and exec: "(ta, \<sigma>') \<in> exec P t' \<sigma>" 
    and [simp]: "\<sigma> = (xcp, h, f # Frs)"
    by(rule jvmd_NormalE)
  obtain xcp' h' frs' where [simp]: "\<sigma>' = (xcp', h', frs')" by(cases \<sigma>', auto)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by(cases f, blast)
  from exec nt have [simp]: "xcp = None" by(cases xcp, auto)
  from `\<Phi> \<turnstile> t': \<sigma> \<surd>` obtain Ts T mxs mxl0 ins xt ST LT 
    where "hconf h"
    and "P,h \<turnstile> t' \<surd>t"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastsimp simp add: correct_state_def)
  from wf red conf nt
  obtain h frs a stk loc C M pc M' n ta' va h'
    where ha: "typeof_addr h a \<noteq> None" and ta: "ta = extTA2JVM P ta'"
    and \<sigma>': "\<sigma>' = extRet2JVM n h' stk loc C M pc frs va"
    and rel: "(ta', va, h') \<in> red_external_aggr P t' a M' (rev (take n stk)) h"
    and ec: "is_external_call P (the (typeof_addr h a)) M'"
    by -(erule (2) exec_new_threadE, fastsimp+)
  from nt ta obtain x' where "NewThread t x' m \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>" by auto
  from red_external_aggr_new_thread_exists_thread_object[OF rel ec ha this] \<sigma>'
  show ?thesis by(cases va) auto
qed

lemma correct_state_ts_thread_conf:
  "correct_state_ts \<Phi> (thr s) (shr s) \<Longrightarrow> thread_conf P (thr s) (shr s)"
by(erule ts_ok_mono)(auto simp add: correct_state_def)

end

context JVM_heap_conf_base' begin

lemma mexecdT_NewThread_Thread_Object:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts \<Phi> (thr s) (shr s); P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr (shr s') t = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(frule correct_state_ts_thread_conf)
apply(erule execd_mthr.redT.cases)
 apply(hypsubst)
 apply(frule (2) execd_tconf.redT_updTs_preserves[where ln'="redT_updLns (locks s) t' no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"])
  apply clarsimp
 apply(clarsimp)
 apply(drule execd_NewThread_Thread_Object)
    apply(drule (1) ts_okD)
    apply(fastsimp)
   apply(assumption)
  apply(fastsimp)
 apply(clarsimp)
apply(simp)
done

end
(*
context JVM_progress begin

lemma execd_Suspend_ex_Interrupted_Notified:
  assumes wf: "wf_prog wf_md P"
  and "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and Suspend: "Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
  and hext: "h' \<unlhd> h''"
  and tconf: "P,h \<turnstile> t \<surd>t"
  shows "\<exists>ta e'' s''. P,t \<turnstile> Normal (xcp', h'', frs') -ta-jvmd\<rightarrow> Normal s'' \<and> Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {}"
  (is "?thesis1")
  and "\<exists>ta e'' s''. P,t \<turnstile> Normal (xcp', h'', frs') -ta-jvmd\<rightarrow> Normal s'' \<and> Interrupted \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {}"
  (is "?thesis2")
proof -
  note [simp] = ta_upd_simps
  from `P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')` Suspend
  obtain stk loc C M pc FRS where [simp]: "xcp = None" "frs = (stk, loc, C, M, pc) # FRS"
    and check: "check P (xcp, h, (stk, loc, C, M, pc) # FRS)"
    and red: "(ta, xcp', h', frs') \<in> exec P t (None, h, (stk, loc, C, M, pc) # FRS)"
    by(cases xcp)(fastsimp elim!: jvmd_NormalE)+
  with Suspend have "?thesis1 \<and> ?thesis2"
  proof(cases "instrs_of P C M ! pc")
    case (Invoke M' n)
    with red Suspend obtain ta' where [simp]: "xcp' = None" "frs' = (stk, loc, C, M, pc) # FRS" "ta = extTA2JVM P ta'"
      and stkn: "stk ! n \<noteq> Null"
      and red': "(ta', RetStaySame, h') \<in> red_external_aggr P t (the_Addr (stk ! n)) M' (rev (take n stk)) h"
      and iec: "is_external_call P (the (typeof_addr h (the_Addr (stk ! n)))) M'"
      by(auto split: split_if_asm simp add: split_def)(frule red_external_aggr_Suspend_StaySame, fastsimp, fastsimp, fastsimp)
    from check iec Invoke stkn obtain a T T'
      where stkn: "stk ! n = Addr a" and T: "typeof_addr h a = \<lfloor>T\<rfloor>"
      and wtext: "P,h \<turnstile> the_Addr (stk ! n)\<bullet>M'(rev (take n stk)) : T'"
      by(auto simp add: check_def split_beta is_Ref_def)
    from red' have "P,t \<turnstile> \<langle>the_Addr (stk ! n)\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>RetStaySame, h'\<rangle>"
      unfolding WT_red_external_list_conv[OF wf wtext tconf] .
    from red_external_Suspend_Notified_Interrupted[OF wf this, of w h''] hext Suspend
    obtain va' va'' h''' ta'' ta''' h''''
      where "P,t \<turnstile> \<langle>the_Addr (stk ! n)\<bullet>M'(rev (take n stk)), h''\<rangle> -ta''\<rightarrow>ext \<langle>va',h'''\<rangle>"
      and Notified: "Notified \<in> set \<lbrace>ta''\<rbrace>\<^bsub>w\<^esub>" "collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> = {}"
      and "P,t \<turnstile> \<langle>the_Addr (stk ! n)\<bullet>M'(rev (take n stk)), h''\<rangle> -ta'''\<rightarrow>ext \<langle>va'',h''''\<rangle>"
      and Interrupted: "Interrupted \<in> set \<lbrace>ta'''\<rbrace>\<^bsub>w\<^esub>" "collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> = {}"
      by auto
    hence "(ta'', va', h''') \<in> red_external_aggr P t (the_Addr (stk ! n)) M' (rev (take n stk)) h''"
      and "(ta''', va'', h'''') \<in> red_external_aggr P t (the_Addr (stk ! n)) M' (rev (take n stk)) h''"
      by(auto intro: red_external_imp_red_external_aggr)
    moreover note stkn T
    moreover from `P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')` tconf
    have "h \<unlhd> h'" by(auto dest!: tconfD intro: exec_1_d_hext)
    hence "h \<unlhd> h''" using hext by(rule hext_trans)
    hence T': "typeof_addr h'' a = \<lfloor>T\<rfloor>" using T by(rule typeof_addr_hext_mono)
    ultimately have "P,t \<turnstile> (xcp, h'', frs') -extTA2JVM P ta''-jvm\<rightarrow> (extRet2JVM n h''' stk loc C M pc FRS va')"
                 "P,t \<turnstile> (xcp, h'', frs') -extTA2JVM P ta'''-jvm\<rightarrow> (extRet2JVM n h'''' stk loc C M pc FRS va'')"
      using Invoke iec
      by -(cases ta'', case_tac [2] ta''', auto simp add: exec_1_iff)
    moreover have "check P (xcp', h'', frs')" using check Invoke iec T T' stkn `h \<unlhd> h''`
      by(clarsimp simp add: check_def)(auto dest: external_WT'_hext_mono)
    ultimately have "P,t \<turnstile> Normal (xcp, h'', frs') -extTA2JVM P ta''-jvmd\<rightarrow> Normal (fst (extRet2JVM n h''' stk loc C M pc FRS va'), fst (snd (extRet2JVM n h''' stk loc C M pc FRS va')), snd (snd (extRet2JVM n h''' stk loc C M pc FRS va')))"
      "P,t \<turnstile> Normal (xcp, h'', frs') -extTA2JVM P ta'''-jvmd\<rightarrow> Normal (fst (extRet2JVM n h'''' stk loc C M pc FRS va''), fst (snd (extRet2JVM n h'''' stk loc C M pc FRS va'')), snd (snd (extRet2JVM n h'''' stk loc C M pc FRS va'')))"
      by(auto simp add: exec_d_def exec_1_iff intro!: exec_1_d_NormalI)
    moreover have "fst (snd (extRet2JVM n h''' stk loc C M pc FRS va')) = h'''" by(cases va') auto
    moreover have "fst (snd (extRet2JVM n h'''' stk loc C M pc FRS va'')) = h''''" by(cases va'') auto
    ultimately show ?thesis using Notified Interrupted by(auto simp del: split_paired_Ex)
  qed(auto split: split_if_asm simp add: split_beta)
  thus ?thesis1 ?thesis2 by simp_all
qed

end
*)
context JVM_typesafe begin

lemma execd_wf_progress:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and "lock_thread_ok (locks S) (thr S)"
  and "correct_state_ts \<Phi> (thr S) (shr S)"
  and "wset S = empty"
  shows "progress JVM_final (mexecd P) convert_RA S"
proof -
  interpret execd_mthr!: multithreaded_start JVM_final "mexecd P" convert_RA S
    using `lock_thread_ok (locks S) (thr S)` `wset S = empty`
    by(unfold_locales)(auto intro: wset_thread_okI)
  from wf obtain wf_md where wfprog: "wf_prog wf_md P" by(auto dest: wt_jvm_progD)

  show ?thesis
  proof
    fix tta s t x ta x' m'
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
      and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and "mexecd P t (x, shr s) ta (x', m')"
      and wait: "\<not> waiting (wset s t)"
    moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
    ultimately have "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>" "mexecd P t (x, h) ta (x', m')" by auto
    from `correct_state_ts \<Phi> (thr S) (shr S)` Red have "correct_state_ts \<Phi> ts h"
      by(auto dest: preserves_correct_state_d[OF wf])
    from wf obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
    
    from `ts t = \<lfloor>(x, no_wait_locks)\<rfloor>` `mexecd P t (x, h) ta (x', m')`
    obtain xcp frs xcp' frs'
      where "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
      and [simp]: "x = (xcp, frs)" "x' = (xcp', frs')"
      by(cases x, auto)
    then obtain f Frs
      where check: "check P (xcp, h, f # Frs)"
      and [simp]: "frs = f # Frs"
      and exec: "(ta, xcp', m', frs') \<in> exec P t (xcp, h, f # Frs)"
      by(auto elim: jvmd_NormalE)
    with `ts t = \<lfloor>(x, no_wait_locks)\<rfloor>` `correct_state_ts \<Phi> ts h`
    have correct: "\<Phi> \<turnstile> t: (xcp, h, f # Frs) \<surd>" by(auto dest: ts_okD)
    obtain stk loc C M pc where f [simp]: "f = (stk, loc, C, M, pc)" by (cases f)
    from correct obtain Ts T mxs mxl0 ins xt ST LT
      where hconf: "hconf h"
      and tconf: "P, h \<turnstile> t \<surd>t"
      and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
      and wt: "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
      and conf_f: "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
      and confs: "conf_fs P h \<Phi> M (length Ts) T Frs"
      and confxcp: "conf_xcp P h xcp (ins ! pc)"
      and preh: "preallocated h"
      by(fastsimp simp add: correct_state_def)
    
    have "\<exists>ta' \<sigma>'. P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -ta'-jvmd\<rightarrow> Normal \<sigma>' \<and>
                  final_thread.actions_ok' (ls, (ts, h), ws) t ta' \<and> final_thread.actions_subset ta' ta"
    proof(cases "final_thread.actions_ok' (ls, (ts, h), ws) t ta")
      case True
      have "final_thread.actions_subset ta ta" ..
      with True `P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')`
      show ?thesis by auto
    next
      case False
      note naok = this
      have ws: "wset s t = None \<or> 
                (\<exists>n a T w. ins ! pc = Invoke wait n \<and> stk ! n = Addr a \<and> typeof_addr h a = \<lfloor>T\<rfloor> \<and> is_external_call P T wait \<and> wset s t = \<lfloor>WokenUp w\<rfloor> \<and> xcp = None)"
      proof(cases "wset s t")
        case None thus ?thesis ..
      next
        case (Some w)
        from execd_mthr.in_wait_SuspendD[OF Red `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` this] `wset S = empty`
        obtain xcp0 frs0 h0 ta0 w' s1 tta1
          where red0: "mexecd P t ((xcp0, frs0), h0) ta0 ((xcp, frs), shr s1)"
          and Suspend: "Suspend w' \<in> set \<lbrace>ta0\<rbrace>\<^bsub>w\<^esub>"
          and s1: "P \<turnstile> s1 -\<triangleright>tta1\<rightarrow>\<^bsub>jvmd\<^esub>* s"
          by auto
        from mexecd_Suspend_Invoke[OF red0 Suspend] sees
        obtain n a T where [simp]: "ins ! pc = Invoke wait n" "xcp = None" "stk ! n = Addr a"
          and type: "typeof_addr h0 a = \<lfloor>T\<rfloor>"
          and iec: "is_external_call P T wait"
          by auto

        from red0 have "h0 \<unlhd> shr s1" by(auto dest: exec_1_d_hext)
        also from s1 have "shr s1 \<unlhd> shr s" by(rule Execd_hext)
        finally have "typeof_addr (shr s) a = \<lfloor>T\<rfloor>" using type
          by(rule typeof_addr_hext_mono)
        moreover from Some wait s obtain w' where "ws t = \<lfloor>WokenUp w'\<rfloor>"
          by(auto simp add: not_waiting_iff)
        ultimately show ?thesis using iec s by auto
      qed

      from ws naok exec sees
      show ?thesis
      proof(cases "ins ! pc")
        case (Invoke M' n)
        from ws show ?thesis
        proof
          assume wst: "wset s t = None"
          with Invoke check exec sees naok obtain a Ts U Ta Us
	    where a: "stk ! n = Addr a"
	    and n: "n < length stk"
	    and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
	    and iec: "is_external_call P Ta M'"
	    and wtext: "P \<turnstile> Ta\<bullet>M'(Us) :: U"
            and sub: "P \<turnstile> Ts [\<le>] Us"
	    and Ts: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Ts"
            and [simp]: "xcp = None"
            by(cases xcp)(fastsimp simp add: is_Ref_def has_method_def external_WT'_iff check_def lock_ok_las'_def split: split_if_asm dest: external_call_not_sees_method)+

          from exec iec Ta n a sees Invoke obtain ta' va m''
	    where exec': "(ta', va, m'') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
	    and ta: "ta = extTA2JVM P ta'"
	    and va: "(xcp', m', frs') = extRet2JVM n m'' stk loc C M pc Frs va"
	    by(auto)
          from va have [simp]: "m'' = m'" by(cases va) simp_all
          from Ta Ts wtext sub have wtext': "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : U" by(rule external_WT'.intros)
          with wfp exec' tconf have red: "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
	    by(simp add: WT_red_external_list_conv)
          from wst have "wset s t = None \<or> M' = wait \<and> (\<exists>w. wset s t = \<lfloor>WokenUp w\<rfloor>)" ..
          with wfp red tconf hconf obtain ta'' va' h''
	    where red': "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h\<rangle> -ta''\<rightarrow>ext \<langle>va',h''\<rangle>"
	    and ok': "final_thread.actions_ok' s t ta''"
	    and sub: "final_thread.actions_subset ta'' ta'"
	    by(rule red_external_wf_red)
          from red' a n Ta iec Invoke sees
          have "(extTA2JVM P ta'', extRet2JVM n h'' stk loc C M pc Frs va') \<in> exec P t (xcp, h, f # Frs)" 
	    by(force intro: red_external_imp_red_external_aggr)
          with check have "P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -extTA2JVM P ta''-jvmd\<rightarrow> Normal (extRet2JVM n h'' stk loc C M pc Frs va')"
	    by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
          moreover from ok' have "final_thread.actions_ok' (ls, (ts, h), ws) t (extTA2JVM P ta'')"
	    by(simp add: final_thread.actions_ok'_convert_extTA)
          moreover from sub ta have "final_thread.actions_subset (extTA2JVM P ta'') ta"
	    by(auto elim: final_thread.actions_subset.cases del: subsetI)
          ultimately show ?thesis by blast
        next
          assume "\<exists>n a T w. ins ! pc = Invoke wait n \<and> stk ! n = Addr a \<and> typeof_addr h a = \<lfloor>T\<rfloor> \<and> is_external_call P T wait \<and> wset s t = \<lfloor>WokenUp w\<rfloor> \<and> xcp = None"
          with Invoke obtain T a w where Invoke: "ins ! pc = Invoke wait n"
            and [simp]: "M' = wait"
            and stkn: "stk ! n = Addr a"
            and T: "typeof_addr h a = \<lfloor>T\<rfloor>"
            and iec: "is_external_call P T wait"
            and wst: "wset s t = \<lfloor>WokenUp w\<rfloor>"
            and [simp]: "xcp = None" by auto
          from exec iec stkn T sees Invoke obtain ta' va m''
	    where exec': "(ta', va, m'') \<in> red_external_aggr P t a wait (rev (take n stk)) h"
	    and ta: "ta = extTA2JVM P ta'"
	    and va: "(xcp', m', frs') = extRet2JVM n m'' stk loc C M pc Frs va" by(auto)
          from va have [simp]: "m'' = m'" by(cases va) simp_all
          from Invoke check sees stkn iec T obtain U
            where "P,h \<turnstile> a\<bullet>wait(rev (take n stk)) : U" by(auto simp add: check_def)
          with wfp tconf exec' have red: "P,t \<turnstile> \<langle>a\<bullet>wait(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
            by(simp add: WT_red_external_list_conv)
          from wst have "wset s t = None \<or> wait = wait \<and> (\<exists>w. wset s t = \<lfloor>WokenUp w\<rfloor>)" by simp
          with wfp red tconf hconf obtain ta'' va' h''
	    where red': "P,t \<turnstile> \<langle>a\<bullet>wait(rev (take n stk)),h\<rangle> -ta''\<rightarrow>ext \<langle>va',h''\<rangle>"
	    and ok': "final_thread.actions_ok' s t ta''"
	    and sub: "final_thread.actions_subset ta'' ta'"
	    by(rule red_external_wf_red)
          from red' stkn T iec Invoke sees
          have "(extTA2JVM P ta'', extRet2JVM n h'' stk loc C M pc Frs va') \<in> exec P t (xcp, h, f # Frs)" 
	    by(force intro: red_external_imp_red_external_aggr)
          with check have "P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -extTA2JVM P ta''-jvmd\<rightarrow> Normal (extRet2JVM n h'' stk loc C M pc Frs va')"
	    by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
          moreover from ok' have "final_thread.actions_ok' (ls, (ts, h), ws) t (extTA2JVM P ta'')"
	    by(simp add: final_thread.actions_ok'_convert_extTA)
          moreover from sub ta have "final_thread.actions_subset (extTA2JVM P ta'') ta"
	    by(auto elim: final_thread.actions_subset.cases del: subsetI)
          ultimately show ?thesis by blast
        qed
      next
        case MEnter
        with exec sees naok ws have False
          by(cases xcp)(auto split: split_if_asm simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
        thus ?thesis ..
      next
        case MExit
        with exec sees False check ws obtain a where [simp]: "hd stk = Addr a" "xcp = None" "ws t = None"
	  and ta: "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a\<rbrace> \<or> ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
	  by(cases xcp)(fastsimp split: split_if_asm simp add: lock_ok_las'_def finfun_upd_apply is_Ref_def check_def)+
        from ta show ?thesis
        proof(rule disjE)
	  assume ta: "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a\<rbrace>"
	  let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
	  from ta exec sees MExit obtain \<sigma>'
	    where "(?ta', \<sigma>') \<in> exec P t (xcp, h, f # Frs)" by auto
	  with check have "P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -?ta'-jvmd\<rightarrow> Normal \<sigma>'"
	    by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
	  moreover from False ta have "has_locks (ls\<^sub>f a) t = 0"
            by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
	  hence "final_thread.actions_ok' (ls, (ts, h), ws) t ?ta'"
	    by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
	  moreover from ta have "final_thread.actions_subset ?ta' ta"
	    by(auto simp add: final_thread.actions_subset_iff collect_locks'_def finfun_upd_apply ta_upd_simps)
	  ultimately show ?thesis by(fastsimp simp add: ta_upd_simps)
        next
	  assume ta: "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
	  let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a\<rbrace>"
	  from ta exec sees MExit obtain \<sigma>'
	    where "(?ta', \<sigma>') \<in> exec P t (xcp, h, f # Frs)" by auto
	  with check have "P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -?ta'-jvmd\<rightarrow> Normal \<sigma>'"
	    by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
	  moreover from False ta have "has_lock (ls\<^sub>f a) t"
            by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
	  hence "final_thread.actions_ok' (ls, (ts, h), ws) t ?ta'"
	    by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
	  moreover from ta have "final_thread.actions_subset ?ta' ta"
	    by(auto simp add: final_thread.actions_subset_iff collect_locks'_def finfun_upd_apply ta_upd_simps)
	  ultimately show ?thesis by(fastsimp simp add: ta_upd_simps)
        qed
      qed(case_tac [!] xcp, auto simp add: split_beta lock_ok_las'_def split: split_if_asm)
    qed
    thus "\<exists>ta' x' m'. mexecd P t (x, shr s) ta' (x', m') \<and> final_thread.actions_ok' s t ta' \<and> final_thread.actions_subset ta' ta"
      by fastsimp
  next
    fix tta s t x w
    assume "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = \<lfloor>WokenUp w\<rfloor>"
    from execd_mthr.in_wait_SuspendD[OF this] `wset S = empty`
    obtain xcp0 frs0 h0 ta0 w' s1 tta1 xcp frs
      where [simp]: "x = (xcp, frs)"
      and red0: "mexecd P t ((xcp0, frs0), h0) ta0 ((xcp, frs), shr s1)"
      and Suspend: "Suspend w' \<in> set \<lbrace>ta0\<rbrace>\<^bsub>w\<^esub>"
      by(cases x)(auto, fastsimp)
    from mexecd_Suspend_Invoke[OF red0 Suspend]
    show "\<not> JVM_final x" by auto
  next
    fix tta s t x ln
    assume "thr s t = \<lfloor>(x, ln)\<rfloor>"
      and "\<not> JVM_final x"
      and Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
    ultimately have "ts t = \<lfloor>(x, ln)\<rfloor>" by simp
    from Red `correct_state_ts \<Phi> (thr S) (shr S)`
    have "correct_state_ts \<Phi> ts h"
      by(auto dest: preserves_correct_state_d[OF wf])
    obtain xcp frs where "x = (xcp, frs)" by (cases x, auto)
    with `\<not> JVM_final x` obtain f Frs where "frs = f # Frs"
      by(fastsimp simp add: neq_Nil_conv)
    with `ts t = \<lfloor>(x, ln)\<rfloor>` `correct_state_ts \<Phi> ts h` `x = (xcp, frs)`
    have "\<Phi> \<turnstile> t: (xcp, h, f # Frs) \<surd>" by(auto dest: ts_okD)
    with `wf_jvm_prog\<^sub>\<Phi> P`
    have "exec_d P t (xcp, h, f # Frs) \<noteq> TypeError" by(auto dest: no_type_error)
    then obtain \<Sigma> where "exec_d P t (xcp, h, f # Frs) = Normal \<Sigma>" by(auto)
    hence "exec P t (xcp, h, f # Frs) = \<Sigma>"
      by(auto simp add: exec_d_def check_def split: split_if_asm)
    with progress[OF wf `\<Phi> \<turnstile> t: (xcp, h, f # Frs) \<surd>`]
    obtain ta \<sigma> where "(ta, \<sigma>) \<in> \<Sigma>" unfolding exec_1_iff by blast
    with `x = (xcp, frs)` `frs = f # Frs` `\<Phi> \<turnstile> t: (xcp, h, f # Frs) \<surd>`
      `wf_jvm_prog\<^sub>\<Phi> P` `exec_d P t (xcp, h, f # Frs) = Normal \<Sigma>`
    show "\<exists>ta x' m'. mexecd P t (x, shr s) ta (x', m')"
      by(cases ta, cases \<sigma>)(fastsimp simp add: split_paired_Ex intro: exec_1_d_NormalI)
  qed
qed

end

context JVM_conf_read begin

lemma mexecT_eq_mexecdT:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and cs: "correct_state_ts \<Phi> (thr s) (shr s)"
  shows "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s' = P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
proof(rule iffI)
  assume "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'"
  thus "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  proof(cases rule: exec_mthr.redT_elims[consumes 1, case_names normal acquire])
    case (normal x x' m')
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` cs
    have "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from mexec_eq_mexecd[OF wf `\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>`] `mexec P t (x, shr s) ta (x', m')`
    have "mexecd P t (x, shr s) ta (x', m')" by simp
    moreover from lifting_wf.redT_updTs_preserves[OF lifting_wf_correct_state_d[OF wf] cs, OF this `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>`] `thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>`
    have "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))) m'" by simp
    ultimately show ?thesis using normal 
      by(cases s')(erule execd_mthr.redT_normal, auto)
  next
    case acquire thus ?thesis
      apply(cases s', clarify)
      apply(rule execd_mthr.redT_acquire, assumption+)
      by(auto)
  qed
next
  assume "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  thus "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'"
  proof(cases rule: execd_mthr.redT_elims[consumes 1, case_names normal acquire])
    case (normal x x' m')
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` cs
    have "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from mexec_eq_mexecd[OF wf `\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>`] `mexecd P t (x, shr s) ta (x', m')`
    have "mexec P t (x, shr s) ta (x', m')" by simp
    moreover from lifting_wf.redT_updTs_preserves[OF lifting_wf_correct_state_d[OF wf] cs, OF `mexecd P t (x, shr s) ta (x', m')` `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>`] `thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>`
    have "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))) m'" by simp
    ultimately show ?thesis using normal
      by(cases s')(erule exec_mthr.redT_normal, auto)
  next
    case acquire thus ?thesis
      apply(cases s', clarify)
      apply(rule exec_mthr.redT_acquire, assumption+)
      by(auto)
  qed
qed

lemma mExecT_eq_mExecdT:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and ct: "correct_state_ts \<Phi> (thr s) (shr s)"
  shows "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s' = P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
proof
  assume Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  thus "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'" using ct
  proof(induct rule: exec_mthr.RedT_induct[consumes 1, case_names refl step])
    case refl thus ?case by auto
  next
    case (step s ttas s' t ta s'')
    hence "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'" by blast
    moreover from `correct_state_ts \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
    have "correct_state_ts \<Phi> (thr s') (shr s')"
      by(auto dest: preserves_correct_state[OF wf])
    with `P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s''` have "P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s''"
      by(unfold mexecT_eq_mexecdT[OF wf])
    ultimately show ?case
      by(blast intro: execd_mthr.RedTI rtrancl3p_step elim: execd_mthr.RedTE)
  qed
next
  assume Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  thus "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'" using ct
  proof(induct rule: execd_mthr.RedT_induct[consumes 1, case_names refl step])
    case refl thus ?case by auto
  next
    case (step s ttas s' t ta s'')
    hence "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'" by blast
    moreover from `correct_state_ts \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
    have "correct_state_ts \<Phi> (thr s') (shr s')"
      by(auto dest: preserves_correct_state_d[OF wf])
    with `P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s''` have "P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s''"
      by(unfold mexecT_eq_mexecdT[OF wf])
    ultimately show ?case
      by(blast intro: exec_mthr.RedTI rtrancl3p_step elim: exec_mthr.RedTE)
  qed
qed

lemma mexecT_preserves_thread_conf: 
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts \<Phi> (thr s) (shr s);
    P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'; thread_conf P (thr s) (shr s) \<rbrakk> 
  \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(simp only: mexecT_eq_mexecdT)(rule execd_tconf.redT_preserves)

lemma mExecT_preserves_thread_conf: 
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts \<Phi> (thr s) (shr s);
    P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s'; thread_conf P (thr s) (shr s) \<rbrakk>
  \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(simp only: mExecT_eq_mExecdT)(rule execd_tconf.RedT_preserves)

end

context JVM_typesafe begin

lemma exec_wf_progress:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and "lock_thread_ok (locks S) (thr S)"
  and csS: "correct_state_ts \<Phi> (thr S) (shr S)"
  and "wset S = empty"
  shows "progress JVM_final (mexec P) convert_RA S"
proof -
  interpret progress!: progress JVM_final "mexecd P" convert_RA S
    using assms by(rule execd_wf_progress)
  show ?thesis
  proof(unfold_locales)
    from `wset S = empty` show "wset_thread_ok (wset S) (thr S)" by(auto intro: wset_thread_okI)
  next
    show "lock_thread_ok (locks S) (thr S)" by fact
  next
    fix tta s t x ta x' m'
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s"
      and thr: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and "mexec P t (x, shr s) ta (x', m')"
      and wait: "\<not> waiting (wset s t)"
    moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
    moreover obtain xcp frs m where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    ultimately have "ts t = \<lfloor>((xcp, frs), no_wait_locks)\<rfloor>" "mexec P t ((xcp, frs), h) ta (x', m')" by auto
    from Red `correct_state_ts \<Phi> (thr S) (shr S)` have css: "correct_state_ts \<Phi> (thr s) (shr s)"
      by(auto dest: preserves_correct_state[OF wf])
    with `ts t = \<lfloor>((xcp, frs), no_wait_locks)\<rfloor>` have "\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
      by(auto dest: ts_okD)
    from `mexec P t (x, shr s) ta (x', m')` have "mexecd P t (x, shr s) ta (x', m')"
      by(simp add: mexec_eq_mexecd[OF wf `\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>`, simplified])
    moreover from Red have "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s" by(unfold mExecT_eq_mExecdT[OF wf csS])
    ultimately have "\<exists>ta' x' m'. mexecd P t (x, shr s) ta' (x', m') \<and> final_thread.actions_ok' s t ta' \<and>
                              final_thread.actions_subset ta' ta"
      using Red thr wait by-(rule progress.wf_red)
    then obtain ta' x' m'
      where "mexecd P t (x, shr s) ta' (x', m')"
      and ta': "final_thread.actions_ok' s t ta'" "final_thread.actions_subset ta' ta"
      by blast
    from `mexecd P t (x, shr s) ta' (x', m')` have "mexec P t (x, shr s) ta' (x', m')"
      by(simp add: mexec_eq_mexecd[OF wf `\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>`, simplified])
    with ta' show "\<exists>ta' x' m'. mexec P t (x, shr s) ta' (x', m') \<and> final_thread.actions_ok' s t ta' \<and> final_thread.actions_subset ta' ta"
      by(blast)
  next
    fix tta s t x w
    assume "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s" "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = \<lfloor>WokenUp w\<rfloor>"
    thus "\<not> JVM_final x" unfolding mExecT_eq_mExecdT[OF wf csS] 
      by(rule progress.red_wait_set_not_final)
  next
    fix tta s t x ln
    assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "\<not> JVM_final x"
      and Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s"
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    with `\<not> JVM_final x` obtain f Frs where [simp]: "frs = f # Frs"
      by(fastsimp simp add: neq_Nil_conv)
    from csS Red have "correct_state_ts \<Phi> (thr s) (shr s)"
      by(auto dest: preserves_correct_state[OF wf])
    with `thr s t = \<lfloor>(x, ln)\<rfloor>` have "\<Phi> \<turnstile> t: (xcp, shr s, f # Frs) \<surd>" by(auto dest: ts_okD)
    from progress[OF wf this]
    show "\<exists>ta x' m'. mexec P t (x, shr s) ta (x', m')"
      by(fastsimp)
  qed
qed

theorem mexecd_TypeSafety:
  fixes ln :: "addr \<Rightarrow>\<^isub>f nat"
  assumes "wf_jvm_prog\<^sub>\<Phi> P"
  and "correct_state_ts \<Phi> (thr s) (shr s)"
  and "lock_thread_ok (locks s) (thr s)"
  and "wset s = empty"
  and "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  and "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'')"
  and "thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>"
  shows "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<Longrightarrow> multithreaded_base.deadlocked JVM_final (mexecd P) s' t"
  and "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>"
proof -
  interpret progress JVM_final "mexecd P" convert_RA s
    by(rule execd_wf_progress) fact+

  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
  have "correct_state_ts \<Phi> (thr s') (shr s')"
    by(fastsimp dest: lifting_wf.RedT_preserves[OF lifting_wf_correct_state_d])
  from `lock_thread_ok (locks s) (thr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
  have "lock_thread_ok (locks s') (thr s')"
    by(fastsimp intro: execd_mthr.RedT_preserves_lock_thread_ok)
  from `correct_state_ts \<Phi> (thr s') (shr s')`
    `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>`
  show cst: "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>" by(auto dest: ts_okD)

  assume nfin: "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks"
  from nfin `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` have "final_thread.not_final_thread JVM_final s' t"
    by(auto simp: final_thread.not_final_thread_iff)
  show "multithreaded_base.deadlocked JVM_final (mexecd P) s' t"
  proof(rule ccontr)
    assume "\<not> multithreaded_base.deadlocked JVM_final (mexecd P) s' t"
    with `wf_jvm_prog\<^sub>\<Phi> P` `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` `final_thread.not_final_thread JVM_final s' t`
      `correct_state_ts \<Phi> (thr s) (shr s)` `lock_thread_ok (locks s) (thr s)` `wset s = empty` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
    have "\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s''"
      by -(erule (1) redT_progress_deadlocked', blast dest: execd_mthr.deadlocked'D2)
    with `\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'')`
    show False ..
  qed
qed

theorem mexec_TypeSafety:
  fixes ln :: "addr \<Rightarrow>\<^isub>f nat"
  assumes "wf_jvm_prog\<^sub>\<Phi> P"
  and "correct_state_ts \<Phi> (thr s) (shr s)"
  and "lock_thread_ok (locks s) (thr s)"
  and "wset s = empty"
  and "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  and "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'')"
  and "thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>"
  shows "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<Longrightarrow> multithreaded_base.deadlocked JVM_final (mexec P) s' t"
  and "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>"
proof -
  interpret progress JVM_final "mexec P" convert_RA s
    by(rule exec_wf_progress) fact+

  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
  have "correct_state_ts \<Phi> (thr s') (shr s')"
    by(fastsimp elim: lifting_wf.RedT_preserves[OF lifting_wf_correct_state])
  from `lock_thread_ok (locks s) (thr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
  have "lock_thread_ok (locks s') (thr s')"
    by(fastsimp intro: exec_mthr.RedT_preserves_lock_thread_ok)
  from `correct_state_ts \<Phi> (thr s') (shr s')`
    `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>`
  show cst: "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>" by(auto dest: ts_okD)

  assume "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks"
  with `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` have "final_thread.not_final_thread JVM_final s' t"
    by(auto simp: final_thread.not_final_thread_iff)
  show "multithreaded_base.deadlocked JVM_final (mexec P) s' t"
  proof(rule ccontr)
    assume "\<not> multithreaded_base.deadlocked JVM_final (mexec P) s' t"
    with `wf_jvm_prog\<^sub>\<Phi> P` `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` `final_thread.not_final_thread JVM_final s' t`
      `correct_state_ts \<Phi> (thr s) (shr s)` `lock_thread_ok (locks s) (thr s)` `wset s = empty` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
    have "\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s''"
      by -(erule (1) redT_progress_deadlocked', blast dest: exec_mthr.deadlocked'D2)
    with `\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'')`
    show False ..
  qed
qed

end

context JVM_heap_conf_base begin

definition correct_jvm_state :: "ty\<^isub>P \<Rightarrow> (addr,thread_id,jvm_thread_state,'heap,addr) state \<Rightarrow> bool"
where
  "correct_jvm_state \<Phi> s
  \<longleftrightarrow> correct_state_ts \<Phi> (thr s) (shr s) \<and> lock_thread_ok (locks s) (thr s) \<and> wset_thread_ok (wset s) (thr s)"

end

context JVM_heap_conf begin

lemma correct_jvm_state_initial:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and start: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = m in C"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  shows "correct_jvm_state \<Phi> (JVM_start_state P C M vs)"
using assms BV_correct_initial[OF wf start sees conf]
apply(cases m)
apply(auto simp add: correct_jvm_state_def start_state_def JVM_start_state'_def intro: lock_thread_okI wset_thread_okI ts_okI split: split_if_asm)
done

end

context JVM_typesafe begin

lemma correct_jvm_state_preserved:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and correct: "correct_jvm_state \<Phi> s"
  and red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  shows "correct_jvm_state \<Phi> s'"
using correct preserves_correct_state[OF wf red]
  exec_mthr.RedT_preserves_lock_thread_ok[OF red]
  exec_mthr.RedT_preserves_wset_thread_ok[OF red]
by(simp add: correct_jvm_state_def)

theorem jvm_typesafe:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and start: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = m in C"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  and exec: "P \<turnstile> JVM_start_state P C M vs -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  shows "correct_jvm_state \<Phi> s'"
by(rule correct_jvm_state_preserved[OF wf _ exec])(rule correct_jvm_state_initial[OF wf start sees conf])

end

end