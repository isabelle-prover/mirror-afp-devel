(*  Title:      JinjaThreads/BV/JVMDeadlocked.thy
    Author:     Andreas Lochbihler
*)
header{* Progress result for both of the multithreaded JVMs *}

theory BVProgressThreaded
imports "../Framework/FWProgress" "../Framework/FWLiftingSem" BVNoTypeError "../JVM/JVMThreaded"
begin


lemma mexec_final_wf: "final_thread_wf JVM_final (mexec P)"
proof(unfold_locales)
  fix x m ta x' m'
  assume "JVM_final x" "mexec P (x, m) ta (x', m')"
  moreover obtain xcp frs tls where x: "x = (xcp, frs)" by (cases x, auto)
  ultimately have "frs = []" by simp
  moreover have "\<not> P \<turnstile> (xcp, m, []) -ta-jvm\<rightarrow> (fst x', m', snd x')"
    by(simp add: exec_1_iff)
  ultimately show False using `mexec P (x, m) ta (x', m')` x by(auto)
qed

interpretation exec_mthr_final: final_thread_wf JVM_final "mexec P"
by(rule mexec_final_wf)

lemma mexecd_final_wf: "final_thread_wf JVM_final (mexecd P)"
proof(unfold_locales)
  fix x m ta x' m'
  assume "JVM_final x" "mexecd P (x, m) ta (x', m')"
  moreover obtain xcp frs where x: "x = (xcp, frs)" by (cases x, auto)
  ultimately have "frs = []" by simp
  moreover have "\<not> P \<turnstile> Normal (xcp, m, []) -ta-jvmd\<rightarrow> Normal (fst x', m', snd x')"
    by(auto elim!: exec_1_d.cases simp add: exec_d_def split: split_if_asm)
  ultimately show False using `mexecd P (x, m) ta (x', m')` x by(auto)
qed

interpretation execd_mthr_final: final_thread_wf JVM_final "mexecd P"
by(rule mexecd_final_wf)

lemma mexec_eq_mexecd: "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; P,\<Phi> \<turnstile> (xcp, h, frs) \<surd> \<rbrakk> \<Longrightarrow> mexec P ((xcp, frs), h) = mexecd P ((xcp, frs), h)"
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



syntax
  can_sync_syntax :: "jvm_prog \<Rightarrow> addr option \<times> heap \<times> frame list \<Rightarrow> (addr + thread_id) set \<Rightarrow> bool" ("_ \<turnstile> \<langle>_\<rangle>/ _/ \<wrong>" [50,0,0] 81)

translations
  "P \<turnstile> \<langle>\<sigma>\<rangle> L \<wrong>" => "multithreaded.can_sync ((CONST mexec) P) (fst \<sigma>, snd (snd \<sigma>)) (fst (snd \<sigma>)) L"
  "P \<turnstile> \<langle>(xcp, h, frs)\<rangle> L \<wrong>" <= "multithreaded.can_sync ((CONST mexec) P) (xcp, frs) h L"

syntax
  must_sync_syntax :: "jvm_prog \<Rightarrow> addr option \<times> heap \<times> frame list \<Rightarrow> bool" ("_ \<turnstile> \<langle>_\<rangle>/ \<wrong>" [50,0] 81)

translations
  "P \<turnstile> \<langle>\<sigma>\<rangle> \<wrong>" => "multithreaded.must_sync ((CONST mexec) P) (fst \<sigma>, snd (snd \<sigma>)) (fst (snd \<sigma>))"
  "P \<turnstile> \<langle>(xcp, h, frs)\<rangle> \<wrong>" <= "multithreaded.must_sync ((CONST mexec) P) (xcp, frs) h"

syntax
  can_sync_d_syntax :: "jvm_prog \<Rightarrow> addr option \<times> heap \<times> frame list \<Rightarrow> (addr + thread_id) set \<Rightarrow> bool" ("_ \<turnstile> \<langle>_\<rangle>\<^isub>d/ _/ \<wrong>" [50,0,0] 81)

translations
  "P \<turnstile> \<langle>\<sigma>\<rangle>\<^isub>d L \<wrong>" => "multithreaded.can_sync ((CONST mexecd) P) (fst \<sigma>, snd (snd \<sigma>)) (fst (snd \<sigma>)) L"
  "P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d L \<wrong>" <= "multithreaded.can_sync ((CONST mexecd) P) (xcp, frs) h L"

syntax
  must_sync_d_syntax :: "jvm_prog \<Rightarrow> addr option \<times> heap \<times> frame list \<Rightarrow> bool" ("_ \<turnstile> \<langle>_\<rangle>\<^isub>d/ \<wrong>" [50,0] 81)

translations
  "P \<turnstile> \<langle>\<sigma>\<rangle>\<^isub>d \<wrong>" => "multithreaded.must_sync ((CONST mexecd) P) (fst \<sigma>, snd (snd \<sigma>)) (fst (snd \<sigma>))"
  "P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d \<wrong>" <= "multithreaded.must_sync ((CONST mexecd) P) (xcp, frs) h"

(* conformance lifted to multithreaded case *)

abbreviation
  correct_state_ts :: "jvm_prog \<Rightarrow> ty\<^isub>P \<Rightarrow> (addr,thread_id,jvm_thread_state) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "correct_state_ts P \<Phi> \<equiv> ts_ok (\<lambda>(xcp, frstls) h. P,\<Phi> \<turnstile> (xcp, h, frstls) \<surd>)"


lemma invoke_new_thread:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl0,ins,xt) in C"
  and "ins ! pc = Invoke Type.start 0"
  and "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  and "P,\<Phi> \<turnstile> (None, h, (stk, loc, C, M, pc) # frs) \<surd>"
  and "h a = \<lfloor>Obj D fs\<rfloor>"
  and "P \<turnstile> D \<preceq>\<^sup>* Thread"
  and "P \<turnstile> D sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'"
  shows "P,\<Phi> \<turnstile> (None, h, [([], Addr a # replicate mxl0' arbitrary, D', run, 0)]) \<surd>"
proof -
  from `P,\<Phi> \<turnstile> (None, h, (stk, loc, C, M, pc) # frs) \<surd>`
  have "P \<turnstile> h \<surd>" by(simp add: correct_state_def)
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
  have "conf_f P h ([], LT') ins' ([], Addr a # replicate mxl0' arbitrary, D', run, 0)"
  proof -
    let ?LT = "OK (Class D') # (replicate mxl0' Err)"
    have "P,h \<turnstile> replicate mxl' arbitrary [:\<le>\<^sub>\<top>] replicate mxl' Err" by simp
    also from `P \<turnstile> D sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'`
    have "P \<turnstile> D \<preceq>\<^sup>* D'" by(rule sees_method_decl_above)
    with `h a = \<lfloor>Obj D fs\<rfloor>` have "P,h \<turnstile> Addr a :\<le> Class D'"
      by(simp add: conf_def)
    ultimately have "P,h \<turnstile> Addr a # replicate mxl0' arbitrary [:\<le>\<^sub>\<top>] ?LT" by(simp)
    also from `wt_start P D' [] mxl0' (\<Phi> D' run)` LT'
    have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT'" by(simp add: wt_start_def)
    finally have "P,h \<turnstile> Addr a # replicate mxl0' arbitrary [:\<le>\<^sub>\<top>] LT'" .
    with `ins' \<noteq> []` show ?thesis by(simp add: conf_f_def)
  qed
  ultimately show ?thesis using `P \<turnstile> D' sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'`
    by(fastsimp simp add: correct_state_def)
qed

lemma exec_new_threadE:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and "P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and "correct_state P \<Phi> \<sigma>"
  and "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []"
  obtains h frs a stk loc C M pc Ts T mxs mxl0 ins xt M' n ao Ta ta' va  Us U m'
  where "\<sigma> = (None, h, (stk, loc, C, M, pc) # frs)"
  and "(ta, \<sigma>') \<in> set (exec P (None, h, (stk, loc, C, M, pc) # frs))"
  and "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
  and "stk ! n = Addr a"
  and "ins ! pc = Invoke M' n"
  and "n < length stk"
  and "h a = \<lfloor>ao\<rfloor>"
  and "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
  and "is_external_call P Ta M' n"
  and "ta = extTA2JVM P ta'"
  and "\<sigma>' = extRet2JVM n m' stk loc C M pc frs va"
  and "(ta', va, m') \<in> set (red_external_list P a M' (rev (take n stk)) h)"
  and "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us"
  and "P \<turnstile> Ta\<bullet>M'(Us) :: U"
proof -
  from `P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'` obtain h f Frs xcp
    where check: "check P \<sigma>"
    and exec: "(ta, \<sigma>') \<in> set (exec P \<sigma>)"
    and [simp]: "\<sigma> = (xcp, h, f # Frs)"
    by(rule jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)"
    by(cases f, blast)
  from `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` exec have [simp]: "xcp = None" by(cases xcp) auto
  from `correct_state P \<Phi> \<sigma>`
  obtain Ts T mxs mxl0 ins xt ST LT 
    where "P \<turnstile> h \<surd>"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastsimp simp add: correct_state_def)
  from check `\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>` sees
  have checkins: "check_instr (ins ! pc) P h stk loc C M pc Frs"
    by(clarsimp simp add: check_def)
  from sees `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` exec obtain M' n where [simp]: "ins ! pc = Invoke M' n"
    by(cases "ins ! pc", auto split: split_if_asm simp add: split_beta)
  from `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P` obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
  
  from checkins have "n < length stk" "is_Ref (stk ! n)" by auto
  moreover from exec sees `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` have "stk ! n \<noteq> Null" by auto
  with `is_Ref (stk ! n)` obtain a where "stk ! n = Addr a"
    by(auto simp add: is_Ref_def elim: is_AddrE)
  moreover with checkins obtain ao where [simp]: "h a = \<lfloor>ao\<rfloor>" by(clarsimp)
  moreover then obtain Ta where Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>" by(fastsimp split: heapobj.splits)
  moreover with checkins exec sees `n < length stk` `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` `stk ! n = Addr a`
  obtain Us U where "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us" "P \<turnstile> Ta\<bullet>M'(Us) :: U" "is_external_call P Ta M' n"
    by(auto elim!: is_ArrE simp add: min_def split_beta has_method_def split: split_if_asm dest: external_call_not_sees_method[OF wfp])
  moreover with `typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>` `n < length stk` exec sees `stk ! n = Addr a`
  obtain ta' va h' where "ta = extTA2JVM P ta'" "\<sigma>' = extRet2JVM n h' stk loc C M pc Frs va"
    "(ta', va, h') \<in> set (red_external_list P a M' (rev (take n stk)) h)"
    by(fastsimp simp add: min_def)
  ultimately show thesis using exec sees by-(rule that, auto)
qed

lemma correct_state_new_thread:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and red: "P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and cs: "correct_state P \<Phi> \<sigma>"
  and nt: "NewThread t'' (xcp, frs) h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "P,\<Phi> \<turnstile> (xcp, h'', frs) \<surd>"
proof -
  from nt have "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []" by auto
  with wf red cs
  obtain h Frs a stk loc C M pc Ts T mxs mxl0 ins xt M' n ao Ta ta' va h' Us U
    where [simp]: "\<sigma> = (None, h, (stk, loc, C, M, pc) # Frs)"
    and exec: "(ta, \<sigma>') \<in> set (exec P (None, h, (stk, loc, C, M, pc) # Frs))"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and [simp]: "stk ! n = Addr a"
    and [simp]: "ins ! pc = Invoke M' n"
    and n: "n < length stk"
    and [simp]: "h a = \<lfloor>ao\<rfloor>"
    and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
    and iec: "is_external_call P Ta M' n"
    and ta: "ta = extTA2JVM P ta'"
    and \<sigma>': "\<sigma>' = extRet2JVM n h' stk loc C M pc Frs va"
    and rel: "(ta', va, h') \<in> set (red_external_list P a M' (rev (take n stk)) h)"
    and Us: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us"
    and wtext: "P \<turnstile> Ta\<bullet>M'(Us) :: U"
    by(rule exec_new_threadE)
  from rel have red: "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>" unfolding red_external_list_conv .
  from ta nt obtain D M'' a' where nt': "NewThread t'' (D, M'', a') h'' \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>"
    "(xcp, frs) = extNTA2JVM P (D, M'', a')" by auto
  with red have [simp]: "h'' = h'" by-(rule red_ext_new_thread_heap)
  from red_external_new_thread_sub_thread[OF red nt'(1)]
  obtain fs where h't'': "h' a' = \<lfloor>Obj D fs\<rfloor>" "P \<turnstile> D \<preceq>\<^sup>* Thread" and [simp]: "M'' = run" by auto
  from wt_jvm_progD[OF wf] obtain wf_md where wfp: "wf_prog wf_md P" ..
  from sub_Thread_sees_run[OF wfp `P \<turnstile> D \<preceq>\<^sup>* Thread`] obtain mxs' mxl0' ins' xt' D'
    where seesrun: "P \<turnstile> D sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'" by auto
  with nt' ta nt have "xcp = None" "frs = [([],Addr a' # replicate mxl0' arbitrary,D',run,0)]"
    by(auto simp add: extNTA2JVM_def split_beta)
  moreover
  have "P,\<Phi> \<turnstile> (None, h', [([], Addr a' # replicate mxl0' arbitrary, D', run, 0)]) \<surd>"
  proof -
    from cs have "P \<turnstile> h \<surd>" by(simp add: correct_state_def)
    with red Ta Us wtext have "P \<turnstile> h' \<surd>" by(rule external_call_hconf)
    moreover from seesrun
    have seesrun': "P \<turnstile> D' sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'"
      by(rule sees_method_idemp)
    moreover with `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P`
    obtain "wt_start P D' [] mxl0' (\<Phi> D' run)" "ins' \<noteq> []"
      by (auto dest: wt_jvm_prog_impl_wt_start)    
    then obtain LT' where "\<Phi> D' run ! 0 = Some ([], LT')"
      by (clarsimp simp add: wt_start_def defs1 sup_state_opt_any_Some)
    moreover
    have "conf_f P h' ([], LT') ins' ([], Addr a' # replicate mxl0' arbitrary, D', run, 0)"
    proof -
      let ?LT = "OK (Class D') # (replicate mxl0' Err)"
      from seesrun have "P \<turnstile> D \<preceq>\<^sup>* D'" by(rule sees_method_decl_above)
      hence "P,h' \<turnstile> Addr a' # replicate mxl0' arbitrary [:\<le>\<^sub>\<top>] ?LT"
	using h't'' by(simp add: conf_def)
      also from `wt_start P D' [] mxl0' (\<Phi> D' run)` `\<Phi> D' run ! 0 = Some ([], LT')`
      have "P \<turnstile> ?LT [\<le>\<^sub>\<top>] LT'" by(simp add: wt_start_def)
      finally have "P,h' \<turnstile> Addr a' # replicate mxl0' arbitrary [:\<le>\<^sub>\<top>] LT'" .
      with `ins' \<noteq> []` show ?thesis by(simp add: conf_f_def)
    qed
    ultimately show ?thesis by(fastsimp simp add: correct_state_def)
  qed
  ultimately show ?thesis by(clarsimp)
qed

lemma correct_state_heap_change:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and red: "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and cs: "P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>"
  and cs'': "P,\<Phi> \<turnstile> (xcp'', h, frs'') \<surd>"
  shows "P,\<Phi> \<turnstile> (xcp'', h', frs'') \<surd>"
proof(cases xcp)
  case None
  with red have "hext h h'" by (auto intro: exec_1_d_hext)
  from `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P` cs red have "P,\<Phi> \<turnstile> (xcp', h', frs') \<surd>"
    by(auto elim!: jvmd_NormalE intro: BV_correct_1 simp add: exec_1_iff)
  from red have "hext h h'" by(auto dest: jvmd_NormalD intro: exec_1_d_hext)
  show ?thesis
  proof(cases frs'')
    case Nil thus ?thesis by(simp add: correct_state_def)
  next
    case (Cons f'' Frs'')
    obtain stk'' loc'' C0'' M0'' pc''
      where "f'' = (stk'', loc'', C0'', M0'', pc'')"
      by(cases f'', blast)
    with `frs'' = f'' # Frs''` cs''
    obtain Ts'' T'' mxs'' mxl\<^isub>0'' ins'' xt'' ST'' LT'' 
      where "P \<turnstile> h \<surd>"
      and sees'': "P \<turnstile> C0'' sees M0'': Ts''\<rightarrow>T'' = (mxs'', mxl\<^isub>0'', ins'', xt'') in C0''"
      and "\<Phi> C0'' M0'' ! pc'' = \<lfloor>(ST'', LT'')\<rfloor>"
      and "conf_f P h (ST'', LT'') ins'' (stk'', loc'', C0'', M0'', pc'')"
      and "conf_fs P h \<Phi> M0'' (length Ts'') T'' Frs''"
      by(fastsimp simp add: correct_state_def)
    
    have "P \<turnstile> h' \<surd>"
    proof(cases frs')
      case Cons
      with `P,\<Phi> \<turnstile> (xcp', h', frs') \<surd>` show ?thesis
	by(simp add: correct_state_def)
    next
      case Nil
      have  "h = h'"
      proof -
	from red `frs' = Nil` obtain f Frs
	  where "check P (xcp, h, frs)"
	  and "P \<turnstile> (xcp, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])"
	  and "frs = f # Frs"
	  by(auto elim: jvmd_NormalE simp add: exec_1_iff)
	moreover obtain stk loc C0 M0 pc
	  where "f = (stk, loc, C0, M0, pc)" by(cases f, blast)
	moreover with `frs = f # Frs` `xcp = None` cs
	obtain Ts T mxs mxl\<^isub>0 ins xt ST LT
	  where "P \<turnstile> C0 sees M0:Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0"
	  and "\<Phi> C0 M0 ! pc = \<lfloor>(ST, LT)\<rfloor>"
	  and "conf_f P h (ST, LT) ins (stk, loc, C0, M0, pc)"
	  and "conf_fs P h \<Phi> M0 (length Ts) T Frs"
	  by(fastsimp simp add: correct_state_def)
	ultimately have "P \<turnstile> C0 has M0" 
	  and "pc < length ins"
	  and "length stk \<le> mxs"
	  and xcpci: "xcp = None \<longrightarrow> check_instr (ins ! pc) P h stk loc C0 M0 pc Frs"
	  by(auto simp add: check_def)
	show ?thesis
	proof(cases xcp')
	  case (Some a)
	  with `P \<turnstile> (xcp, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])` `f = (stk, loc, C0, M0, pc)`
	  show "h = h'" by(cases xcp)(auto dest: exec_instr_xcp_unchanged simp add: exec_1_iff)
	next
	  case None
	  show ?thesis
	  proof(cases xcp)
	    case Some
	    with `P \<turnstile> (xcp, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])` `f = (stk, loc, C0, M0, pc)`
	    show ?thesis by(auto simp add: exec_1_iff)
	  next
	    case None
	    with xcpci have "check_instr (ins ! pc) P h stk loc C0 M0 pc Frs" ..
	    with None `xcp' = None` `P \<turnstile> (xcp, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])` `f = (stk, loc, C0, M0, pc)`
	      `P \<turnstile> C0 sees M0:Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0`
	    have "ins ! pc = Return"
	      by(clarsimp simp add: exec_1_iff)(cases "ins ! pc", auto split: split_if_asm sum.split_asm simp add: split_beta extRet2JVM_def[folded sum_case_def])
	    with `P \<turnstile> (xcp, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])` `xcp = None`
	      `f = (stk, loc, C0, M0, pc)` `P \<turnstile> C0 sees M0:Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0`
	    show ?thesis
	      by(auto simp add: exec_1_iff split: split_if_asm simp add: split_beta)
	  qed
	qed
      qed
      with `P \<turnstile> h \<surd>` show ?thesis by simp
    qed
    thus ?thesis using Cons `P,\<Phi> \<turnstile> (xcp'', h, frs'') \<surd>` `hext h h'`
      apply(cases xcp'')
      apply(auto simp add: correct_state_def)
      apply(blast dest: hext_objD intro: conf_fs_hext conf_f_hext)+
      done
  qed
next
  case (Some a)
  with `P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')` have "h = h'" by(auto elim!: jvmd_NormalE)
  with `P,\<Phi> \<turnstile> (xcp'', h, frs'') \<surd>` show ?thesis by simp
qed


lemma lifting_wf_correct_state_d: "wf_jvm_prog\<^sub>\<Phi> P \<Longrightarrow> lifting_wf (mexecd P) (\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>)"
apply(unfold_locales)
by(auto intro: BV_correct_d_1 correct_state_new_thread correct_state_heap_change)

lemma lifting_wf_correct_state:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  shows "lifting_wf (mexec P) (\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>)"
proof(unfold_locales)
  fix x m ta x' m'
  assume "mexec P (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x m"
  with wf show "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x' m'"
    apply(cases x, cases x', simp add: welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`])
    by(rule BV_correct_d_1)
next
  fix x m ta x' m' t'' x''
  assume "mexec P (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x m"
    and "NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  with wf show "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x'' m'"
    apply(cases x, cases x', cases x'', clarify, unfold welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`])
    by(rule correct_state_new_thread)
next
  fix x m ta x' m' x''
  assume "mexec P (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x m"
    and "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x'' m"
  with wf show "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x'' m'"
    apply(cases x, cases x', cases x'', clarify, unfold welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`])
    by(rule correct_state_heap_change)
qed

declare split_paired_Ex [simp del]

lemmas preserves_correct_state = FWLiftingSem.lifting_wf.RedT_preserves[OF lifting_wf_correct_state]
lemmas preserves_correct_state_d = FWLiftingSem.lifting_wf.RedT_preserves[OF lifting_wf_correct_state_d]


lemma execd_NewThread_Thread_Object:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and conf: "correct_state P \<Phi> \<sigma>"
  and red: "P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and nt: "NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "\<exists>C fs. fst (snd \<sigma>') t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> Class C \<le> Class Thread"
proof -
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(blast dest: wt_jvm_progD)
  from red obtain h f Frs xcp
    where check: "check P \<sigma>" 
    and exec: "(ta, \<sigma>') \<in> set (exec P \<sigma>)" 
    and [simp]: "\<sigma> = (xcp, h, f # Frs)"
    by(rule jvmd_NormalE)
  obtain xcp' h' frs' where [simp]: "\<sigma>' = (xcp', h', frs')" by(cases \<sigma>', auto)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by(cases f, blast)
  from exec nt have [simp]: "xcp = None" by(cases xcp, auto)
  from `correct_state P \<Phi> \<sigma>` obtain Ts T mxs mxl0 ins xt ST LT 
    where "P \<turnstile> h \<surd>"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastsimp simp add: correct_state_def)
  from wf red conf nt
  obtain h frs a stk loc C M pc M' n ao ta' va h'
    where ha: "h a = \<lfloor>ao\<rfloor>" and ta: "ta = extTA2JVM P ta'"
    and \<sigma>': "\<sigma>' = extRet2JVM n h' stk loc C M pc frs va"
    and rel: "(ta', va, h') \<in> set (red_external_list P a M' (rev (take n stk)) h)"
    by -(erule (2) exec_new_threadE, clarsimp)
  from nt ta obtain x' where "NewThread t x' m \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>" by auto
  from red_external_new_thread_exists_thread_object[OF rel[folded red_external_list_conv] this] ha \<sigma>'
  show ?thesis by(cases va) auto
qed

lemma mexecdT_NewThread_Thread_Object:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr s) (shr s); P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>C fs. shr s' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> Class C \<le> Class Thread"
apply(erule execd_mthr.redT.cases)
 apply(clarsimp)
 apply(drule execd_NewThread_Thread_Object)
    apply(drule ts_okD, assumption)
    apply(fastsimp)
   apply(assumption)
  apply(fastsimp)
 apply(simp)
apply(simp)
done

lemma mexecdT_preserves_thread_conf:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and cs: "correct_state_ts P \<Phi> (thr s) (shr s)"
  and red: "P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  and tc: "thread_conf P (thr s) (shr s)"
  shows "thread_conf P (thr s') (shr s')"
proof(rule thread_confI)
  fix t xln
  assume tst': "thr s' t = \<lfloor>xln\<rfloor>"
  obtain e x ln where xln [simp]: "xln = ((e, x), ln)" by(cases xln, auto)
  show "\<exists>T. typeof\<^bsub>shr s'\<^esub> (Addr t) = \<lfloor>T\<rfloor> \<and> P \<turnstile> T \<le> Class Thread"
  proof(cases "thr s t")
    case None
    with red tst' have nt: "NewThread t (e, x) (shr s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" 
      and [simp]: "ln = no_wait_locks" by(auto dest: execd_mthr.redT_new_thread)
    from mexecdT_NewThread_Thread_Object[OF wf cs red nt]
    obtain C fs where "shr s' t = \<lfloor>Obj C fs\<rfloor>" "P \<turnstile> Class C \<le> Class Thread" by blast
    thus ?thesis by(clarsimp)
  next
    case (Some Xln)
    with tc obtain T where "typeof\<^bsub>shr s\<^esub> (Addr t) = \<lfloor>T\<rfloor>" "P \<turnstile> T \<le> Class Thread"
      by(rule thread_confDE)
    moreover from red have "hext (shr s) (shr s')"
      by(auto intro: execd_hext)
    ultimately have "typeof\<^bsub>shr s'\<^esub> (Addr t) = \<lfloor>T\<rfloor>"
      by(blast dest: type_of_hext_type_of hext_objarrD)
    with `P \<turnstile> T \<le> Class Thread` show ?thesis by blast
  qed
qed

lemma mExecdT_preserves_thread_conf:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  shows "\<lbrakk> P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s'; correct_state_ts P \<Phi> (thr s) (shr s); thread_conf P (thr s) (shr s) \<rbrakk> \<Longrightarrow> thread_conf P (thr s') (shr s')"
proof(induct rule: execd_mthr.RedT_induct[consumes 1, case_names refl step])
  case refl thus ?case by simp
next
  case (step s tta s' t ta s'')
  from wf show ?case
  proof(rule mexecdT_preserves_thread_conf)
    from `P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s'` `correct_state_ts P \<Phi> (thr s) (shr s)`
    show "correct_state_ts P \<Phi> (thr s') (shr s')" by(rule preserves_correct_state_d[OF wf])
  next
    from `thread_conf P (thr s) (shr s)` `correct_state_ts P \<Phi> (thr s) (shr s)`
      `\<lbrakk>correct_state_ts P \<Phi> (thr s) (shr s); thread_conf P (thr s) (shr s)\<rbrakk> \<Longrightarrow> thread_conf P (thr s') (shr s')`
    show "thread_conf P (thr s') (shr s')" by blast
  next
    show "execd_mthr.redT P s' (t, ta) s''" by fact
  qed
qed

lemma execd_wf_red:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and "lock_thread_ok (locks S) (thr S)"
  and "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "wf_red JVM_final (mexecd P) S"
using `lock_thread_ok (locks S) (thr S)`
proof(unfold_locales)
  fix tta s t x ta x' m'
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and "mexecd P (x, shr s) ta (x', m')"
  moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
  ultimately have "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>" "mexecd P (x, h) ta (x', m')" by auto
  from `correct_state_ts P \<Phi> (thr S) (shr S)` Red have "correct_state_ts P \<Phi> ts h"
    by(auto dest: preserves_correct_state_d[OF wf])
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)

  from `ts t = \<lfloor>(x, no_wait_locks)\<rfloor>` `mexecd P (x, h) ta (x', m')`
  obtain xcp frs xcp' frs'
    where "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and [simp]: "x = (xcp, frs)" "x' = (xcp', frs')"
    by(cases x, auto)
  then obtain f Frs
    where check: "check P (xcp, h, f # Frs)"
    and [simp]: "frs = f # Frs"
    and exec: "(ta, xcp', m', frs') \<in> set (exec P (xcp, h, f # Frs))"
    by(auto elim: jvmd_NormalE)
  with `ts t = \<lfloor>(x, no_wait_locks)\<rfloor>` `correct_state_ts P \<Phi> ts h`
  have correct: "P,\<Phi> \<turnstile> (xcp, h, f # Frs) \<surd>" by(auto dest: ts_okD)
  obtain stk loc C M pc where f [simp]: "f = (stk, loc, C, M, pc)" by (cases f)
  from correct obtain Ts T mxs mxl0 ins xt ST LT
    where hconf: "P \<turnstile> h \<surd>"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and wt: "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and conf_f: "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and confs: "conf_fs P h \<Phi> M (length Ts) T Frs"
    and confxcp: "conf_xcp P h xcp (ins ! pc)"
    by(fastsimp simp add: correct_state_def)
  
  have "\<exists>ta' \<sigma>'. P \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -ta'-jvmd\<rightarrow> Normal \<sigma>' \<and>
                    final_thread.actions_ok' (ls, (ts, h), ws) t ta' \<and> final_thread.actions_subset ta' ta"
  proof(cases "final_thread.actions_ok' (ls, (ts, h), ws) t ta")
    case True
    have "final_thread.actions_subset ta ta" ..
    with True `P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')`
    show ?thesis by auto
  next
    case False
    with exec have [simp]: "xcp = None" "ta \<noteq> \<epsilon>" by(auto simp add: lock_ok_las'_def)
      from check sees have ci: "check_instr (ins ! pc) P h stk loc C M pc Frs" by(simp add: check_def)
    from sees exec show ?thesis
    proof(cases "ins ! pc")
      case (Invoke M' n)
      with ci exec sees obtain a ao Ts U Ta 
	where a: "stk ! n = Addr a"
	and n: "n < length stk"
	and ao: "h a = \<lfloor>ao\<rfloor>"
	and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
	and iec: "is_external_call P Ta M' n"
	and wtext: "P \<turnstile> Ta\<bullet>M'(Ts) :: U"
	and Ts: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Ts"
	by(auto simp add: is_Ref_def has_method_def min_def split: split_if_asm heapobj.split_asm elim!: is_ArrE dest: external_call_not_sees_method[OF wfp])
      from exec iec Ta n a sees Invoke obtain ta' va m''
	where exec': "(ta', va, m'') \<in> set (red_external_list P a M' (rev (take n stk)) h)"
	and ta: "ta = extTA2JVM P ta'"
	and va: "(xcp', m', frs') = extRet2JVM n m'' stk loc C M pc Frs va"
	by(auto simp add: min_def)
      from va have [simp]: "m'' = m'" by(cases va) simp_all
      from exec' have red: "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
	unfolding red_external_list_conv by simp
      from red obtain ta'' va' h''
	where red': "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h\<rangle> -ta''\<rightarrow>ext \<langle>va',h''\<rangle>"
	and ok': "final_thread.actions_ok' (ls, (ts, h), ws) t ta''"
	and sub: "final_thread.actions_subset ta'' ta'"
	by(rule red_external_wf_red)
      from red' a n ao Ta iec Invoke sees
      have "(extTA2JVM P ta'', extRet2JVM n h'' stk loc C M pc Frs va') \<in> set (exec P (xcp, h, f # Frs))" 
	by(force simp add: min_def red_external_list_conv)
      with check have "P \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -extTA2JVM P ta''-jvmd\<rightarrow> Normal (extRet2JVM n h'' stk loc C M pc Frs va')"
	by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
      moreover from ok' have "final_thread.actions_ok' (ls, (ts, h), ws) t (extTA2JVM P ta'')"
	by(simp add: final_thread.actions_ok'_convert_extTA)
      moreover from sub ta have "final_thread.actions_subset (extTA2JVM P ta'') ta"
	by(auto elim: final_thread.actions_subset.cases del: subsetI)
      ultimately show ?thesis by blast
    next
      case MEnter
      with exec sees False have False by(auto split: split_if_asm simp add: lock_ok_las'_def finfun_upd_apply)
      thus ?thesis ..
    next
      case MExit
      with exec sees False ci obtain a where [simp]: "hd stk = Addr a"
	and ta: "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace> \<or> ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
	by(fastsimp split: split_if_asm simp add: lock_ok_las'_def finfun_upd_apply is_Ref_def)
      from ta show ?thesis
      proof(rule disjE)
	assume ta: "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>"
	let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
	from ta exec sees MExit obtain \<sigma>'
	  where "(?ta', \<sigma>') \<in> set (exec P (xcp, h, f # Frs))" by auto
	with check have "P \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -?ta'-jvmd\<rightarrow> Normal \<sigma>'"
	  by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
	moreover from False ta have "has_locks (ls\<^sub>f a) t = 0" by(auto simp add: lock_ok_las'_def finfun_upd_apply)
	hence "final_thread.actions_ok' (ls, (ts, h), ws) t ?ta'"
	  by(auto simp add: lock_ok_las'_def finfun_upd_apply)
	moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: final_thread.actions_subset_iff collect_locks'_def finfun_upd_apply)
	ultimately show ?thesis by fastsimp
      next
	assume ta: "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a\<rbrace>"
	let ?ta' = "\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a\<rbrace>"
	from ta exec sees MExit obtain \<sigma>'
	  where "(?ta', \<sigma>') \<in> set (exec P (xcp, h, f # Frs))" by auto
	with check have "P \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -?ta'-jvmd\<rightarrow> Normal \<sigma>'"
	  by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
	moreover from False ta have "has_lock (ls\<^sub>f a) t" by(auto simp add: lock_ok_las'_def finfun_upd_apply)
	hence "final_thread.actions_ok' (ls, (ts, h), ws) t ?ta'"
	  by(auto simp add: lock_ok_las'_def finfun_upd_apply)
	moreover from ta have "final_thread.actions_subset ?ta' ta"
	  by(auto simp add: final_thread.actions_subset_iff collect_locks'_def finfun_upd_apply)
	ultimately show ?thesis by fastsimp
      qed
    qed(simp_all add: final_thread.actions_ok'_empty)
  qed
  thus "\<exists>ta' x' m'. mexecd P (x, shr s) ta' (x', m') \<and> final_thread.actions_ok' s t ta' \<and> final_thread.actions_subset ta' ta"
    by fastsimp
qed

lemma mexecT_eq_mexecdT:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and cs: "correct_state_ts P \<Phi> (thr s) (shr s)"
  shows "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s' = P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
proof(rule iffI)
  assume "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'"
  thus "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  proof(induct rule: exec_mthr.redT_elims[consumes 1, case_names normal acquire])
    case (normal x x')
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` cs
    have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from mexec_eq_mexecd[OF wf `P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>`] `mexec P (x, shr s) ta (x', shr s')`
    have "mexecd P (x, shr s) ta (x', shr s')" by simp
    with normal show ?case 
      apply(cases s')
      apply(rule execd_mthr.redT_normal, assumption+)
      by(auto)
  next
    case acquire thus ?case
      apply(cases s', clarify)
      apply(rule execd_mthr.redT_acquire, assumption+)
      by(auto)
  qed
next
  assume "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  thus "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'"
  proof(induct rule: execd_mthr.redT_elims[consumes 1, case_names normal acquire])
    case (normal x x')
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` cs
    have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from mexec_eq_mexecd[OF wf `P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>`] `mexecd P (x, shr s) ta (x', shr s')`
    have "mexec P (x, shr s) ta (x', shr s')" by simp
    with normal show ?case 
      apply(cases s')
      apply(rule exec_mthr.redT_normal, assumption+)
      by(auto)
  next
    case acquire thus ?case
      apply(cases s', clarify)
      apply(rule exec_mthr.redT_acquire, assumption+)
      by(auto)
  qed
qed

lemma mExecT_eq_mExecdT:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and ct: "correct_state_ts P \<Phi> (thr s) (shr s)"
  shows "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s' = P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
proof
  assume Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  thus "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'" using ct
  proof(induct rule: exec_mthr.RedT_induct[consumes 1, case_names refl step])
    case refl thus ?case by auto
  next
    case (step s ttas s' t ta s'')
    from `correct_state_ts P \<Phi> (thr s) (shr s)` `correct_state_ts P \<Phi> (thr s) (shr s) \<Longrightarrow> P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
    have "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'" by blast
    moreover from `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
    have "correct_state_ts P \<Phi> (thr s') (shr s')"
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
    from `correct_state_ts P \<Phi> (thr s) (shr s)` `correct_state_ts P \<Phi> (thr s) (shr s) \<Longrightarrow> P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
    have "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'" by blast
    moreover from `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
    have "correct_state_ts P \<Phi> (thr s') (shr s')"
      by(auto dest: preserves_correct_state_d[OF wf])
    with `P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s''` have "P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s''"
      by(unfold mexecT_eq_mexecdT[OF wf])
    ultimately show ?case
      by(blast intro: exec_mthr.RedTI rtrancl3p_step elim: exec_mthr.RedTE)
  qed
qed

lemma mexecT_preserves_thread_conf: 
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr s) (shr s);
    P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'; thread_conf P (thr s) (shr s) \<rbrakk> 
  \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(simp only: mexecT_eq_mexecdT)(rule mexecdT_preserves_thread_conf)

lemma mExecT_preserves_thread_conf: 
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr s) (shr s);
    P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s'; thread_conf P (thr s) (shr s) \<rbrakk>
  \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(simp only: mExecT_eq_mExecdT)(rule mExecdT_preserves_thread_conf)

lemma exec_wf_red:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and "lock_thread_ok (locks S) (thr S)"
  and csS: "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "wf_red JVM_final (mexec P) S"
proof(unfold_locales)
  from `lock_thread_ok (locks S) (thr S)`
  show "lock_thread_ok (locks S) (thr S)" .
next
  fix tta s t x ta x' m'
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s"
    and thr: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and "mexec P (x, shr s) ta (x', m')"
  moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
  moreover obtain xcp frs m where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have "ts t = \<lfloor>((xcp, frs), no_wait_locks)\<rfloor>" "mexec P ((xcp, frs), h) ta (x', m')" by auto
  from wf `lock_thread_ok (locks S) (thr S)` `correct_state_ts P \<Phi> (thr S) (shr S)`
  have "wf_red JVM_final (mexecd P) S" by(rule execd_wf_red)
  moreover from Red `correct_state_ts P \<Phi> (thr S) (shr S)` have css: "correct_state_ts P \<Phi> (thr s) (shr s)"
    by(auto dest: preserves_correct_state[OF wf])
  with `ts t = \<lfloor>((xcp, frs), no_wait_locks)\<rfloor>` have "P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>"
    by(auto dest: ts_okD)
  from `mexec P (x, shr s) ta (x', m')` have "mexecd P (x, shr s) ta (x', m')"
    by(simp add: mexec_eq_mexecd[OF wf `P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>`, simplified])
  moreover from Red have "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s" by(unfold mExecT_eq_mExecdT[OF wf csS])
  ultimately have "\<exists>ta' x' m'. mexecd P (x, shr s) ta' (x', m') \<and> final_thread.actions_ok' s t ta' \<and>
                            final_thread.actions_subset ta' ta"
    using Red thr by-(rule wf_red.wf_red)
  then obtain ta' x' m'
    where "mexecd P (x, shr s) ta' (x', m')"
    and ta': "final_thread.actions_ok' s t ta'" "final_thread.actions_subset ta' ta"
    by blast
  from `mexecd P (x, shr s) ta' (x', m')` have "mexec P (x, shr s) ta' (x', m')"
    by(simp add: mexec_eq_mexecd[OF wf `P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>`, simplified])
  with ta' show "\<exists>ta' x' m'.
             mexec P (x, shr s) ta' (x', m') \<and> 
             final_thread.actions_ok' s t ta' \<and>
             final_thread.actions_subset ta' ta"
    by(blast)
qed


lemma execd_wf_progress:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and "lock_thread_ok (locks S) (thr S)"
  and "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "wf_progress JVM_final (mexecd P) S"
proof(unfold_locales)
  from `lock_thread_ok (locks S) (thr S)`
  show "lock_thread_ok (locks S) (thr S)" .
next
  fix tta s t x ln
  assume "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "\<not> JVM_final x"
    and Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
  moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
  ultimately have "ts t = \<lfloor>(x, ln)\<rfloor>" by simp
  from Red `correct_state_ts P \<Phi> (thr S) (shr S)`
  have "correct_state_ts P \<Phi> ts h"
    by(auto dest: preserves_correct_state_d[OF wf])
  obtain xcp frs where "x = (xcp, frs)" by (cases x, auto)
  with `\<not> JVM_final x` obtain f Frs where "frs = f # Frs"
    by(fastsimp simp add: neq_Nil_conv)
  with `ts t = \<lfloor>(x, ln)\<rfloor>` `correct_state_ts P \<Phi> ts h` `x = (xcp, frs)`
  have "P,\<Phi> \<turnstile> (xcp, h, f # Frs) \<surd>" by(auto dest: ts_okD)
  with `wf_jvm_prog\<^sub>\<Phi> P`
  have "exec_d P (xcp, h, f # Frs) \<noteq> TypeError" by(auto dest: no_type_error)
  then obtain \<Sigma> where "exec_d P (xcp, h, f # Frs) = Normal \<Sigma>" by(auto)
  hence "exec P (xcp, h, f # Frs) = \<Sigma>"
    by(auto simp add: exec_d_def check_def split: split_if_asm)
  hence "\<Sigma> \<noteq> []" by -(drule sym, auto intro: exec_not_empty del: notI)
  then obtain ta \<sigma> where "(ta, \<sigma>) \<in> set \<Sigma>" by(fastsimp simp add: neq_Nil_conv)
  with `x = (xcp, frs)` `frs = f # Frs` `P,\<Phi> \<turnstile> (xcp, h, f # Frs) \<surd>`
    `wf_jvm_prog\<^sub>\<Phi> P` `exec_d P (xcp, h, f # Frs) = Normal \<Sigma>`
  show "\<exists>ta x' m'. mexecd P (x, shr s) ta (x', m')"
    by(cases ta, cases \<sigma>)(fastsimp simp add: split_paired_Ex intro: exec_1_d_NormalI)
qed

lemma exec_wf_progress:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P" 
  and "lock_thread_ok (locks S) (thr S)"
  and cs: "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "wf_progress JVM_final (mexec P) S"
proof(unfold_locales)
  from `lock_thread_ok (locks S) (thr S)`
  show "lock_thread_ok (locks S) (thr S)" .
next
  fix tta s t x ln
  assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "\<not> JVM_final x"
    and Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s"
  obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  with `\<not> JVM_final x` obtain f Frs where [simp]: "frs = f # Frs"
    by(fastsimp simp add: neq_Nil_conv)
  from cs Red have "correct_state_ts P \<Phi> (thr s) (shr s)"
    by(auto dest: preserves_correct_state[OF wf])
  with `thr s t = \<lfloor>(x, ln)\<rfloor>` have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
  with exec_not_empty[where P=P and h="shr s" and f=f and frs=Frs and xcp=xcp]
  show "\<exists>ta x' m'. mexec P (x, shr s) ta (x', m')"
    by(fastsimp simp add: split_paired_Ex exec_1_iff neq_Nil_conv)
qed


lemma progress_deadlock:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr S) (shr S);
     lock_thread_ok (locks S) (thr S) \<rbrakk> 
  \<Longrightarrow> progress JVM_final (mexec P) S (final_thread_wf.deadlock JVM_final (mexec P))"
apply(rule final_thread_wf.progress_deadlock[OF mexec_final_wf])
apply(rule exec_wf_progress, assumption+)
apply(rule exec_wf_red, assumption+)
done

lemma progress_deadlocked:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr S) (shr S);
     lock_thread_ok (locks S) (thr S) \<rbrakk> 
  \<Longrightarrow> progress JVM_final (mexec P) S (final_thread_wf.deadlocked' JVM_final (mexec P))"
unfolding final_thread_wf.deadlock_eq_deadlocked'[symmetric, OF mexec_final_wf]
by(rule progress_deadlock)

lemma progress_deadlock_d:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr S) (shr S);
     lock_thread_ok (locks S) (thr S) \<rbrakk> 
  \<Longrightarrow> progress JVM_final (mexecd P) S (final_thread_wf.deadlock JVM_final (mexecd P))"
apply(rule final_thread_wf.progress_deadlock[OF mexecd_final_wf])
apply(rule execd_wf_progress, assumption+)
apply(rule execd_wf_red, assumption+)
done

lemma progress_deadlocked_d:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr S) (shr S);
     lock_thread_ok (locks S) (thr S) \<rbrakk> 
  \<Longrightarrow> progress JVM_final (mexecd P) S (final_thread_wf.deadlocked' JVM_final (mexecd P))"
unfolding final_thread_wf.deadlock_eq_deadlocked'[symmetric, OF mexecd_final_wf]
by(rule progress_deadlock_d)

theorem mexecd_TypeSafety:
  fixes ln :: "addr \<Rightarrow>\<^isub>f nat"
  assumes "wf_jvm_prog\<^sub>\<Phi> P"
  and "correct_state_ts P \<Phi> (thr s) (shr s)"
  and "lock_thread_ok (locks s) (thr s)"
  and "thread_conf P (thr s) (shr s)"
  and "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  and "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'')"
  and "thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>"
  shows "thread_conf P (thr s') (shr s')"
  and "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<Longrightarrow> execd_mthr_final.deadlocked P s' t"
  and "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>"
proof -
  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'` `thread_conf P (thr s) (shr s)`
  show "thread_conf P (thr s') (shr s')"
    by-(rule mExecdT_preserves_thread_conf)
  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
  have "correct_state_ts P \<Phi> (thr s') (shr s')"
    by(fastsimp dest: lifting_wf.RedT_preserves[OF lifting_wf_correct_state_d])
  from `lock_thread_ok (locks s) (thr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
  have "lock_thread_ok (locks s') (thr s')"
    by(fastsimp intro: execd_mthr.RedT_preserves_lock_thread_ok)
  from `correct_state_ts P \<Phi> (thr s') (shr s')`
    `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>`
  show cst: "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>" by(auto dest: ts_okD)

  assume nfin: "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks"
  from nfin `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` have "execd_mthr_final.not_final_thread s' t"
    by(auto simp: execd_mthr_final.not_final_thread_iff)
  show "execd_mthr_final.deadlocked P s' t"
  proof(rule ccontr)
    assume "\<not> execd_mthr_final.deadlocked P s' t"
    with `wf_jvm_prog\<^sub>\<Phi> P` `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` `execd_mthr_final.not_final_thread s' t`
      `correct_state_ts P \<Phi> (thr s') (shr s')` `lock_thread_ok (locks s') (thr s')`
    have "\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s''"
      apply -
      apply(rule progress.redT_progress[OF progress_deadlocked_d])
      by(blast dest: execd_mthr_final.deadlocked'D2)+
    with `\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'')`
    show False ..
  qed
qed


theorem mexec_TypeSafety:
  fixes ln :: "addr \<Rightarrow>\<^isub>f nat"
  assumes "wf_jvm_prog\<^sub>\<Phi> P"
  and "correct_state_ts P \<Phi> (thr s) (shr s)"
  and "lock_thread_ok (locks s) (thr s)"
  and "thread_conf P (thr s) (shr s)"
  and "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  and "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'')"
  and "thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>"
  shows "thread_conf P (thr s') (shr s')"
  and "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<Longrightarrow> exec_mthr_final.deadlocked P s' t"
  and "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>"
proof -
  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'` `thread_conf P (thr s) (shr s)`
  show "thread_conf P (thr s') (shr s')"
    by-(rule mExecT_preserves_thread_conf)
next
  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
  have "correct_state_ts P \<Phi> (thr s') (shr s')"
    by(fastsimp elim: lifting_wf.RedT_preserves[OF lifting_wf_correct_state])
  from `lock_thread_ok (locks s) (thr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
  have "lock_thread_ok (locks s') (thr s')"
    by(fastsimp intro: exec_mthr.RedT_preserves_lock_thread_ok)
  from `correct_state_ts P \<Phi> (thr s') (shr s')`
    `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>`
  show cst: "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>" by(auto dest: ts_okD)

  assume "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks"
  with `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` have "exec_mthr_final.not_final_thread s' t"
    by(auto simp: exec_mthr_final.not_final_thread_iff)
  show "exec_mthr_final.deadlocked P s' t"
  proof(rule ccontr)
    assume "\<not> exec_mthr_final.deadlocked P s' t"
    with `wf_jvm_prog\<^sub>\<Phi> P` `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` `exec_mthr_final.not_final_thread s' t`
      `correct_state_ts P \<Phi> (thr s') (shr s')` `lock_thread_ok (locks s') (thr s')`
    have "\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s''"
      apply -
      apply(rule progress.redT_progress[OF progress_deadlocked])
      by(blast dest: exec_mthr_final.deadlocked'D2)+
    with `\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'')`
    show False ..
  qed
qed

end