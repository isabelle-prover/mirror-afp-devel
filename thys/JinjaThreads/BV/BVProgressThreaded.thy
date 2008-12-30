(*  Title:      JinjaThreads/BV/JVMDeadlocked.thy
    Author:     Andreas Lochbihler
*)
theory BVProgressThreaded
imports "../Framework/FWProgress" "../Framework/FWLiftingSem" BVNoTypeError "../JVM/JVMThreaded"
begin


lemma final_interp: "final_thread_wf final (mexec P)"
proof
  fix x m ta x' m'
  assume "final x" "mexec P (x, m) ta (x', m')"
  moreover obtain xcp frs tls where x: "x = (xcp, frs)" by (cases x, auto)
  ultimately have "frs = []" by simp
  moreover have "\<not> P \<turnstile> (xcp, m, []) -ta-jvm\<rightarrow> (fst x', m', snd x')"
    by(simp add: exec_1_iff)
  ultimately show False using `mexec P (x, m) ta (x', m')` x by(auto)
qed

interpretation exec_mthr_final!: final_thread_wf final "mexec P"
by(rule final_interp)

lemma final_interp_d: "final_thread_wf final (mexecd P)"
proof
  fix x m ta x' m'
  assume "final x" "mexecd P (x, m) ta (x', m')"
  moreover obtain xcp frs where x: "x = (xcp, frs)" by (cases x, auto)
  ultimately have "frs = []" by simp
  moreover have "\<not> P \<turnstile> Normal (xcp, m, []) -ta-jvmd\<rightarrow> Normal (fst x', m', snd x')"
    by(auto elim!: exec_1_d.cases simp add: exec_d_def split: split_if_asm)
  ultimately show False using `mexecd P (x, m) ta (x', m')` x by(auto)
qed

interpretation execd_mthr_final!: final_thread_wf final "mexecd P"
by(rule final_interp_d)

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
  shows "P,\<Phi> \<turnstile> (None, h, [([], Addr a # replicate mxl0' undefined, D', run, 0)]) \<surd>"
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
  have "conf_f P h ([], LT') ins' ([], Addr a # replicate mxl0' undefined, D', run, 0)"
  proof -
    let ?LT = "OK (Class D') # (replicate mxl0' Err)"
    have "P,h \<turnstile> replicate mxl' undefined [:\<le>\<^sub>\<top>] replicate mxl' Err" by simp
    also from `P \<turnstile> D sees run:[]\<rightarrow>Void=(mxs', mxl0', ins',xt') in D'`
    have "P \<turnstile> D \<preceq>\<^sup>* D'" by(rule sees_method_decl_above)
    with `h a = \<lfloor>Obj D fs\<rfloor>` have "P,h \<turnstile> Addr a :\<le> Class D'"
      by(simp add: conf_def)
    ultimately have "P,h \<turnstile> Addr a # replicate mxl0' undefined [:\<le>\<^sub>\<top>] ?LT" by(simp)
    also from `wt_start P D' [] mxl0' (\<Phi> D' run)` LT'
    have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT'" by(simp add: wt_start_def)
    finally have "P,h \<turnstile> Addr a # replicate mxl0' undefined [:\<le>\<^sub>\<top>] LT'" .
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
  obtains h frs a stk loc C M pc Ts T mxs mxl0 ins xt D fs mxs' mxl0' ins' xt' D'
  where "\<sigma> = (None, h, (Addr a # stk, loc, C, M, pc) # frs)"
  and "(ta, \<sigma>') \<in> set (exec (P, (None, h, (Addr a # stk, loc, C, M, pc) # frs)))"
  and "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
  and "ins ! pc = Invoke Type.start 0"
  and "h a = \<lfloor>Obj D fs\<rfloor>"
  and "P \<turnstile> D \<preceq>\<^sup>* Thread"
  and "is_class P Thread"
  and "P \<turnstile> D sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'"
proof -
  note elimrule = `\<And>h a stk loc C M pc frs Ts T mxs mxl0 ins xt D fs mxs' mxl0' ins' xt' D'.
    \<lbrakk>\<sigma> = (None, h, (Addr a # stk, loc, C, M, pc) # frs); (ta, \<sigma>') \<in> set (exec (P, None, h, (Addr a # stk, loc, C, M, pc) # frs));
    P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C; ins ! pc = Invoke Type.start 0; h a = \<lfloor>Obj D fs\<rfloor>;
    P \<turnstile> D \<preceq>\<^sup>* Thread; is_class P Thread; P \<turnstile> D sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'\<rbrakk>
    \<Longrightarrow> thesis`
  from `P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'` obtain h f Frs
    where check: "check P \<sigma>"
    and exec: "(ta, \<sigma>') \<in> set (exec (P, \<sigma>))"
    and [simp]: "\<sigma> = (None, h, f # Frs)"
    by(rule jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)"
    by(cases f, blast)
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
  from sees `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` exec have [simp]: "ins ! pc = Invoke Type.start 0"
    by(auto, cases "ins ! pc", auto split: split_if_asm)
  from checkins have "stk \<noteq> []" "is_Ref (stk ! 0)" by auto
  from `stk \<noteq> []` obtain st Stk where [simp]: "stk = st # Stk"
    by(auto simp add: neq_Nil_conv)
  { assume "st = Null"
    with sees exec `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` have False by(auto) }
  with `is_Ref (stk ! 0)`
  obtain a where [simp]: "st = Addr a"
    by(auto simp add: is_Ref_def elim: is_AddrE)
  with checkins obtain D fs where [simp]: "h a = \<lfloor>Obj D fs\<rfloor>" 
    by(clarsimp, blast elim: is_ArrE)
  with sees `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []` exec have "P \<turnstile> D \<preceq>\<^sup>* Thread"
    by(auto split: split_if_asm simp add: split_beta)
  with `P \<turnstile> D \<preceq>\<^sup>* Thread` `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P` checkins
  have "is_class P Thread" unfolding wf_jvm_prog_phi_def
    by(auto simp add: has_method_def dest: Thread_not_sees_method_start)
  with`wf_jvm_prog\<^bsub>\<Phi>\<^esub> P` `P \<turnstile> D \<preceq>\<^sup>* Thread`
  obtain mxs' mxl0' ins' xt' D'
    where "P \<turnstile> D sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'"
    unfolding wf_jvm_prog_phi_def
    by(auto dest: sub_Thread_sees_run)
  with `h a = \<lfloor>Obj D fs\<rfloor>` exec
  show thesis
    by-(rule elimrule[OF _ _ sees `ins ! pc = Invoke Type.start 0` _ `P \<turnstile> D \<preceq>\<^sup>* Thread` `is_class P Thread`], fastsimp+)
qed

lemma correct_state_new_thread:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and red: "P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and cs: "correct_state P \<Phi> \<sigma>"
  and nt: "NewThread t'' (xcp, frs) h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "P,\<Phi> \<turnstile> (xcp, h', frs) \<surd>"
proof -
  from nt have "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []" by auto
  with wf red cs
  obtain h Frs a stk loc C M pc Ts T mxs mxl0 ins xt D fs mxs' mxl0' ins' xt' D'
  where [simp]: "\<sigma> = (None, h, (Addr a # stk, loc, C, M, pc) # Frs)"
    and exec: "(ta, \<sigma>') \<in> set (exec (P, None, h, (Addr a # stk, loc, C, M, pc) # Frs))"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and [simp]: "ins ! pc = Invoke Type.start 0"
    and [simp]: "h a = \<lfloor>Obj D fs\<rfloor>"
    and "P \<turnstile> D \<preceq>\<^sup>* Thread"
    and "is_class P Thread"
    and seesrun: "P \<turnstile> D sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'"
    by(rule exec_new_threadE)
  from sees nt exec
  have execi: "(ta, \<sigma>') \<in> set (exec_instr (Invoke Type.start 0) P h (Addr a # stk) loc C M pc Frs)"
    by(auto split: split_if_asm simp add: split_beta)
  with seesrun nt have "xcp = None" "h' = h" 
    "frs = [([],Addr a # replicate mxl0' undefined,D',run,0)]"
    by(auto split: split_if_asm)
  moreover
  have "P,\<Phi> \<turnstile> (None, h, [([], Addr a # replicate mxl0' undefined, D', run, 0)]) \<surd>"
  proof -
    from cs have "P \<turnstile> h \<surd>" by(simp add: correct_state_def)
    moreover from seesrun
    have seesrun': "P \<turnstile> D' sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'"
      by(rule sees_method_idemp)
    moreover with `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P`
    obtain "wt_start P D' [] mxl0' (\<Phi> D' run)" "ins' \<noteq> []"
      by (auto dest: wt_jvm_prog_impl_wt_start)    
    then obtain LT' where "\<Phi> D' run ! 0 = Some ([], LT')"
      by (clarsimp simp add: wt_start_def defs1 sup_state_opt_any_Some)
    moreover
    have "conf_f P h ([], LT') ins' ([], Addr a # replicate mxl0' undefined, D', run, 0)"
    proof -
      let ?LT = "OK (Class D') # (replicate mxl0' Err)"
      from seesrun have "P \<turnstile> D \<preceq>\<^sup>* D'" by(rule sees_method_decl_above)
      hence "P,h \<turnstile> Addr a # replicate mxl0' undefined [:\<le>\<^sub>\<top>] ?LT"
	by(simp add: conf_def)
      also from `wt_start P D' [] mxl0' (\<Phi> D' run)` `\<Phi> D' run ! 0 = Some ([], LT')`
      have "P \<turnstile> ?LT [\<le>\<^sub>\<top>] LT'" by(simp add: wt_start_def)
      finally have "P,h \<turnstile> Addr a # replicate mxl0' undefined [:\<le>\<^sub>\<top>] LT'" .
      with `ins' \<noteq> []` show ?thesis
	by(simp add: conf_f_def)
    qed
    ultimately show ?thesis
      by(fastsimp simp add: correct_state_def)
  qed
  ultimately show ?thesis by(clarsimp)
qed

lemma correct_state_heap_change:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and red: "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and cs: "P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>"
  and cs'': "P,\<Phi> \<turnstile> (xcp'', h, frs'') \<surd>"
  shows "P,\<Phi> \<turnstile> (xcp'', h', frs'') \<surd>"
proof -
  from red have "xcp = None" by(rule jvmd_NormalE, auto)
  with red have "hext h h'" by (auto intro: exec_1_d_hext)
  from `wf_jvm_prog\<^bsub>\<Phi>\<^esub> P` cs red have "P,\<Phi> \<turnstile> (xcp', h', frs') \<surd>"
    by(auto elim!: jvmd_NormalE intro: BV_correct_1 simp add: exec_1_iff)
  from red have "hext h h'" by(auto dest: jvmd_NormalD intro: exec_1_d_hext)
  show ?thesis
  proof(cases xcp'')
    case Some
    with cs'' show ?thesis by(simp add: correct_state_def)
  next
    case None thus ?thesis
    proof(cases frs'')
      case Nil thus ?thesis by(simp add: correct_state_def)
    next
      case (Cons f'' Frs'')
      obtain stk'' loc'' C0'' M0'' pc''
	where "f'' = (stk'', loc'', C0'', M0'', pc'')"
	by(cases f'', blast)
      with `frs'' = f'' # Frs''` `xcp'' = None` cs''
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
	    and "P \<turnstile> (None, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])"
	    and "xcp = None" "frs = f # Frs"
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
	    and "check_instr (ins ! pc) P h stk loc C0 M0 pc Frs"
	    by(auto simp add: check_def)
	  show ?thesis
	  proof(cases xcp')
	    case (Some a)
	    with `P \<turnstile> (None, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])` 
	      `P \<turnstile> C0 sees M0:Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0` `f = (stk, loc, C0, M0, pc)`
	    have "\<exists>a'. (\<lfloor>a\<rfloor>, h', []) = find_handler P a' h Frs"
	      by(auto simp add: exec_1_iff)
	    thus "h = h'" by(auto elim: find_handler_preserves_heapD)
	  next
	    case None
	    { fix a
	      assume "(None, h', []) = find_handler P a h Frs"
	      hence ?thesis
		by(rule find_handler_preserves_heapD) }
	    moreover
	    { assume "\<And>a. (None, h', []) \<noteq> find_handler P a h Frs"
	      with None `P \<turnstile> (None, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])`
		`f = (stk, loc, C0, M0, pc)` `P \<turnstile> C0 sees M0:Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0`
	      have "ins ! pc = Return"
		by(clarsimp simp add: exec_1_iff, cases "ins ! pc", auto split: split_if_asm simp add: split_beta)
	      with `P \<turnstile> (None, h, f # Frs) -ta-jvm\<rightarrow> (xcp', h', [])`
		`f = (stk, loc, C0, M0, pc)` `P \<turnstile> C0 sees M0:Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0`
	      have ?thesis
		by(auto simp add: exec_1_iff split: split_if_asm simp add: split_beta) }
	    ultimately show ?thesis
	      by blast
	  qed
	qed
	with `P \<turnstile> h \<surd>` show ?thesis by simp
      qed
      thus ?thesis using None Cons `P,\<Phi> \<turnstile> (xcp'', h, frs'') \<surd>` `hext h h'`
	by(fastsimp simp add: correct_state_def intro: conf_f_hext conf_fs_hext)
    qed
  qed
qed


lemma lifting_wf_correct_state_d: "wf_jvm_prog\<^sub>\<Phi> P \<Longrightarrow> lifting_wf (mexecd P) (\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>)"
proof qed (auto intro: BV_correct_d_1 correct_state_new_thread correct_state_heap_change)

lemma lifting_wf_correct_state:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  shows "lifting_wf (mexec P) (\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>)"
proof
  fix x m ta x' m'
  assume "mexec P (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x m"
  with wf show "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x' m'"
    apply(cases x, cases x', simp add: welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`])
    apply (rule BV_correct_d_1)
    apply assumption+
    done
next
  fix x m ta x' m' t'' x''
  assume "mexec P (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x m"
    and "NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  with wf show "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x'' m'"
    apply(cases x, cases x', cases x'', clarify, unfold welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`])
    apply(rule correct_state_new_thread)
    apply assumption+
    done
next
  fix x m ta x' m' x''
  assume "mexec P (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x m"
    and "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x'' m"
  with wf show "(\<lambda>(xcp, frs) h. P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>) x'' m'"
    apply(cases x, cases x', cases x'', clarify, unfold welltyped_commute[symmetric, OF `wf_jvm_prog\<^sub>\<Phi> P`])
    apply(rule correct_state_heap_change)
    apply assumption+
    done
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
  from red obtain h f Frs
    where check: "check P \<sigma>" 
    and exec: "(ta, \<sigma>') \<in> set (exec (P, \<sigma>))" 
    and [simp]: "\<sigma> = (None, h, f # Frs)"
    by(rule jvmd_NormalE)
  obtain xcp' h' frs' where [simp]: "\<sigma>' = (xcp', h', frs')" by(cases \<sigma>', auto)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by(cases f, blast)
  from `correct_state P \<Phi> \<sigma>` obtain Ts T mxs mxl0 ins xt ST LT 
    where "P \<turnstile> h \<surd>"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastsimp simp add: correct_state_def)
  from nt sees exec have [simp]: "ins ! pc = Invoke Type.start 0"
    by(cases "ins ! pc")(fastsimp split: split_if_asm simp add: split_beta)+
  with nt sees exec have "stk ! 0 \<noteq> Null" by(auto)
  with check sees obtain a C' fs'
    where "stk ! 0 = Addr a"
    and "h a = \<lfloor>Obj C' fs'\<rfloor>"
    by(fastsimp simp add: check_def is_Ref_def neq_Nil_conv elim!: is_ArrE)
  with sees exec nt have "a = t" "P \<turnstile> Class C' \<le> Class Thread" "h' = h" 
    by(auto simp add: split_beta split: split_if_asm)
  with `h a = \<lfloor>Obj C' fs'\<rfloor>` show ?thesis by(auto)
qed

lemma mexecdT_NewThread_Thread_Object:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr s) (shr s); P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>C fs. shr s' t = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> Class C \<le> Class Thread"
apply(erule multithreaded.redT.cases)
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
      and [simp]: "ln = no_wait_locks" by(auto dest: multithreaded.redT_new_thread)
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
proof(induct rule: multithreaded.RedT_induct[consumes 1, case_names refl step])
  case refl thus ?case by simp
next
  case (step s tta s' t ta s'')
  from wf show ?case
  proof (rule mexecdT_preserves_thread_conf)
    from `P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s'` `correct_state_ts P \<Phi> (thr s) (shr s)`
    show "correct_state_ts P \<Phi> (thr s') (shr s')" by(rule preserves_correct_state_d[OF wf])
    from `thread_conf P (thr s) (shr s)` `correct_state_ts P \<Phi> (thr s) (shr s)`
      `\<lbrakk>correct_state_ts P \<Phi> (thr s) (shr s); thread_conf P (thr s) (shr s)\<rbrakk> \<Longrightarrow> thread_conf P (thr s') (shr s')`
    show "thread_conf P (thr s') (shr s')" by blast
    show "multithreaded.redT final (mexecd P) s' (t, ta) s''" by fact
  qed
qed


lemma execd_wf_red:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "wf_red final (mexecd P) S"
proof
  fix tta s t x ta x' m'
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and "mexecd P (x, shr s) ta (x', m')"
  moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
  ultimately have "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>" "mexecd P (x, h) ta (x', m')" by auto
  from `correct_state_ts P \<Phi> (thr S) (shr S)` Red have "correct_state_ts P \<Phi> ts h"
    by(auto dest: preserves_correct_state_d[OF wf])

  from `ts t = \<lfloor>(x, no_wait_locks)\<rfloor>` `mexecd P (x, h) ta (x', m')`
  obtain xcp frs xcp' frs'
    where "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and [simp]: "x = (xcp, frs)" "x' = (xcp', frs')"
    by(cases x, auto)
  then obtain f Frs
    where [simp]: "xcp = None"
    and check: "check P (None, h, f # Frs)"
    and [simp]: "frs = f # Frs"
    and exec: "(ta, xcp', m', frs') \<in> set (exec (P, (None, h, f # Frs)))"
    by(auto elim: jvmd_NormalE)
  with `ts t = \<lfloor>(x, no_wait_locks)\<rfloor>` `correct_state_ts P \<Phi> ts h`
  have "P,\<Phi> \<turnstile> (None, h, f # Frs) \<surd>"
    by(auto dest: ts_okD)
  have "\<exists>ta' x' m'. mexecd P (x, h) ta' (x', m') \<and> 
                    thread_oks ts m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and>
                    lock_ok_las' ls t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and>
                    collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
                    final_thread.cond_action_oks' (ls, (ts, m), ws) t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and>
                    final_thread.collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> final_thread.collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
  proof(cases "thread_oks ts m' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>")
    case False
    then obtain xs TA ys 
      where tat: "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys"
      and "thread_oks ts m' xs"
      and nto: "\<not> thread_ok (redT_updTs ts xs) m' TA"
      by(auto simp add: not_thread_oks_conv)
    hence "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []" by simp
    with `P,\<Phi> \<turnstile> (None, h, f # Frs) \<surd>` `frs = f # Frs`
    obtain a stk loc C M pc Ts T mxs mxl0 ins xt D fs mxs' mxl0' ins' xt' D'
      where [simp]: "xcp = None" "f = (Addr a # stk, loc, C, M, pc)"
      and exec': "(ta, xcp', m', frs') \<in> set (exec (P, None, h, (Addr a # stk, loc, C, M, pc) # Frs))"
      and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
      and [simp]: "ins ! pc = Invoke Type.start 0"
      and [simp]: "h a = \<lfloor>Obj D fs\<rfloor>"
      and "P \<turnstile> D \<preceq>\<^sup>* Thread"
      and "is_class P Thread"
      and seesrun: "P \<turnstile> D sees run: []\<rightarrow>Void = (mxs', mxl0', ins', xt') in D'"
      apply -
      apply(rule exec_new_threadE[OF `wf_jvm_prog\<^sub>\<Phi> P` `P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')`])
      by(fastsimp, assumption, blast)
    from exec' sees `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys`
    have [simp]: "xs = []" "ys = []"
      by(auto simp add: split_beta Cons_eq_append_conv append_eq_Cons_conv split: split_if_asm)
    show ?thesis
    proof(cases TA)
      case (NewThread t' X H)
      from NewThread exec' sees seesrun `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys`
      have [simp]: "X = (None, [([], Addr a # replicate mxl0' undefined, D', run, 0)])"
	"H = h" "xcp' = None" "m' = h" "frs' = (Unit # stk, loc, C, M, Suc pc) # Frs" "t' = a"
	by(auto simp add: split_beta Cons_eq_append_conv split: split_if_asm)
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists t'\<rbrace>"
      from `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys` `P \<turnstile> D \<preceq>\<^sup>* Thread` sees
      have "\<exists>\<sigma>'. (?ta', \<sigma>') \<in> set (exec (P, (None, h, f # Frs)))"
	by(auto simp add: split_beta Cons_eq_append_conv)
      then obtain \<sigma>' where "(?ta', \<sigma>') \<in> set (exec (P, (None, h, f # Frs)))" by blast
      with `check P (None, h, f # Frs)`
      have "P \<turnstile> Normal (None, h, f # Frs) -?ta'-jvmd\<rightarrow> Normal \<sigma>'"
	by -(rule exec_1_d_NormalI[where \<Sigma> = "exec (P, None, h, f # Frs)"], simp add: exec_d_def)
      moreover from nto NewThread have "thread_oks ts m' \<lbrace>?ta'\<rbrace>\<^bsub>t\<^esub>" by(auto)
      moreover have "lock_ok_las' ls t \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub>"
	by(auto simp add: lock_ok_las'_def lock_actions_ok'_def)
      moreover
      have "collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> = {}" by(auto elim!: collect_locks'E)
      have "collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
	unfolding `collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> = {}` by auto
      ultimately show ?thesis
	by(cases \<sigma>', fastsimp)
    next
      case NewThreadFail
      with `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys` exec' sees `P \<turnstile> D \<preceq>\<^sup>* Thread`
      have False by(auto split: split_if_asm simp add: split_beta)
      thus ?thesis ..
    next
      case (ThreadExists t')
      let ?ta' = "\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread a (None, [([], Addr a # replicate mxl0' undefined, D', run, 0)]) h\<rbrace>"
      let ?\<sigma>' = "(None, h, (Unit # stk, loc, C, M, Suc pc) # Frs)"
      from ThreadExists exec' sees `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys`
      have [simp]: "t' = a" by(auto split: split_if_asm simp add: split_beta)
      from sees `P \<turnstile> D \<preceq>\<^sup>* Thread` seesrun
      have "(?ta', ?\<sigma>') \<in> set (exec (P, (None, h, f # Frs)))"
	by(auto intro: image_eqI[where x="(?ta', ?\<sigma>')"])
      with `check P (None, h, f # Frs)`
      have "P \<turnstile> Normal (None, h, f # Frs) -?ta'-jvmd\<rightarrow> Normal ?\<sigma>'"
	by - (rule exec_1_d_NormalI[where \<Sigma> = "exec (P, None, h, f # Frs)"], simp add: exec_d_def)
      moreover
      from ThreadExists exec' sees seesrun `\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = xs @ TA # ys`
      have [simp]: "m' = h"
	by(auto simp add: split_beta Cons_eq_append_conv split: split_if_asm dest: find_handler_preserves_heapD)
      from ThreadExists nto have "free_thread_id ts t'" by(auto)
      hence "thread_oks ts m' \<lbrace>?ta'\<rbrace>\<^bsub>t\<^esub>" by(auto)
      moreover
      have "lock_ok_las' ls t \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub>"
	by(auto simp add: lock_ok_las'_def lock_actions_ok'_def)
      moreover
      have "collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> = {}" by(auto elim!: collect_locks'E)
      have "collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
	unfolding `collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> = {}` by auto
      ultimately show ?thesis
	by(fastsimp)
    qed
  next
    case True
    obtain stk loc C0 M0 pc
      where [simp]: "f = (stk, loc, C0, M0, pc)"
      by(cases f, blast)
    with `P,\<Phi> \<turnstile> (None, h, f # Frs) \<surd>`
    obtain Ts T mxs mxl\<^isub>0 ins xt ST LT 
      where "P \<turnstile> h \<surd>"
      and sees: "P \<turnstile> C0 sees M0: Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0"
      and "\<Phi> C0 M0 ! pc = \<lfloor>(ST, LT)\<rfloor>"
      and "conf_f P h (ST, LT) ins (stk, loc, C0, M0, pc)"
      and "conf_fs P h \<Phi> M0 (length Ts) T Frs"
      by(fastsimp simp add: correct_state_def)
    show ?thesis
    proof(cases "lock_ok_las' ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>")
      case True
      with `thread_oks ts m' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>` `mexecd P (x, h) ta (x', m')`
      show ?thesis by(blast intro!: collect_locks'_subset_collect_locks final_thread.cond_action_oks'_True)
    next
      case False
      then obtain l where "\<not> lock_actions_ok (ls l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)" 
	and ml: "\<And>xs ys. \<lbrakk> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ Lock # ys; lock_actions_ok (ls l) t xs \<rbrakk>
                 \<Longrightarrow> may_lock (upd_locks (ls l) t xs) t"
	unfolding not_lock_ok_las'_conv not_lock_actions_ok'_conv by blast
      then obtain xs L ys where "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys"
	"lock_actions_ok (ls l) t xs" "\<not> lock_action_ok (upd_locks (ls l) t xs) t L"
	unfolding not_lock_actions_ok_conv by blast

      with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys` exec `f = (stk, loc, C0, M0, pc)` sees
      show ?thesis
      proof(cases "ins ! pc")
	case (Invoke M n)
	with exec `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys` `f = (stk, loc, C0, M0, pc)` sees
	have M: "M = wait \<or> M = notify \<or> M = notifyAll" 
	  and [simp]: "n = 0"
	  by(auto simp add: split_beta split: split_if_asm)
	from M show ?thesis
	proof(rule disjE)
	  assume [simp]: "M = wait"
	  with Invoke exec `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys` `f = (stk, loc, C0, M0, pc)` sees
	  have tall: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock, ReleaseAcquire] \<or> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
	    by(auto simp add: split_beta split: split_if_asm)
	  thus ?thesis
	  proof(rule disjE)
	    assume tal: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock, ReleaseAcquire]"
	    with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
	    have "xs = [] \<and> L = Unlock \<and> ys = [Lock, ReleaseAcquire] \<or>
  	          xs = [Unlock] \<and> L = Lock \<and> ys = [ReleaseAcquire] \<or> 
	          xs = [Unlock, Lock] \<and> L = ReleaseAcquire \<and> ys = []"
	      by(auto simp add: neq_Nil_conv append_eq_Cons_conv Cons_eq_append_conv)
	    moreover
	    { assume [simp]: "xs = []" "L = Unlock" "ys = [Lock, ReleaseAcquire]"
	      from Invoke tal `check P (None, h, f # Frs)` sees exec `f = (stk, loc, C0, M0, pc)`
	      have "\<exists>\<sigma>'. (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>, \<sigma>') \<in> set (exec (P, (None, h, f # Frs)))"
		by(auto split: split_if_asm)
	      then obtain xcp'' m'' frs'' where "(\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>, xcp'', m'', frs'') \<in> set (exec (P, None, h, f # Frs))"
		by(clarsimp simp only: split_paired_Ex)
	      with `check P (None, h, f # Frs)`
	      have "P \<turnstile> Normal (None, h, f # Frs) -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>-jvmd\<rightarrow> Normal (xcp'', m'', frs'')"
		by(fastsimp intro: exec_1_d_NormalI simp add: exec_d_def)
	      moreover have "thread_oks ts m' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>t\<^esub>" by simp
	      moreover from `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
	      have "\<not> has_lock (ls l) t" by(simp)
	      hence "lock_ok_las' ls t \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub>"
		by(auto simp add: lock_ok_las'_def lock_actions_ok'_def)
	      moreover have "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> {}"
		by(auto elim!: collect_locks'E split: split_if_asm)
	      hence "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
	      ultimately have ?thesis using `x = (xcp, frs)` `frs = f # Frs`
		`f = (stk, loc, C0, M0, pc)` `check P (None, h, f # Frs)`
		`P \<turnstile> C0 sees M0: Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0` `xcp = None`
		by(fastsimp) }
	    moreover
	    { assume xsL: "xs = [Unlock] \<and> L = Lock \<and> ys = [ReleaseAcquire] \<or> 
       	                   xs = [Unlock, Lock] \<and> L = ReleaseAcquire \<and> ys = []"
	      hence False
	      proof(rule disjE)
		assume "xs = [Unlock] \<and> L = Lock \<and> ys = [ReleaseAcquire]"
		then obtain [simp]: "xs = [Unlock]" "L = Lock" "ys = [ReleaseAcquire]" by auto
		with `lock_actions_ok (ls l) t xs` `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
		have "may_lock (upd_locks (ls l) t xs) t"
		  unfolding `L = Lock` by-(rule ml)
		with `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
		show False by(auto)
	      next
		assume "xs = [Unlock, Lock] \<and> L = ReleaseAcquire \<and> ys = []"
		with `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
		show False by(auto)
	      qed }
	    ultimately show ?thesis by blast
	  next
	    assume tal: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
	    with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
	    have [simp]: "xs = []" "L = UnlockFail" "ys = []"
	      by(auto simp add: append_eq_Cons_conv Cons_eq_append_conv)
	    let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub> Suspend l\<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l, ReleaseAcquire\<rightarrow>l\<rbrace>"
	    from Invoke tal `check P (None, h, f # Frs)` sees exec `f = (stk, loc, C0, M0, pc)`
	    have "(?ta', None, h, (Unit # tl stk, loc, C0, M0, pc+1) # Frs) \<in> set (exec (P, (None, h, f # Frs)))"
	      by(auto split: split_if_asm)
	    with `check P (None, h, f # Frs)`
	    have "P \<turnstile> Normal (None, h, f # Frs) -?ta'-jvmd\<rightarrow> Normal (None, h, (Unit # tl stk, loc, C0, M0, pc+1) # Frs)"
	      by(fastsimp intro: exec_1_d_NormalI simp add: exec_d_def)
	    moreover have "thread_oks ts m' \<lbrace>?ta'\<rbrace>\<^bsub>t\<^esub>" by simp
	    moreover from `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
	    have "has_lock (ls l) t" by simp
	    hence "lock_ok_las' ls t \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub>"
	      by(auto simp add: lock_ok_las'_def lock_actions_ok'_def intro!: may_lock_t_may_lock_unlock_lock_t
                      intro: has_lock_may_lock)
	    moreover have "collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> {}"
	      by(auto elim!: collect_locks'E split: split_if_asm)
	    hence "collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
	    ultimately show ?thesis using `x = (xcp, frs)` `frs = f # Frs`
	      `f = (stk, loc, C0, M0, pc)` `check P (None, h, f # Frs)`
	      `P \<turnstile> C0 sees M0: Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0` `xcp = None`
	      by(fastsimp)
	  qed
	next
	  assume M: "M = notify \<or> M = notifyAll"
	  with Invoke exec `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys` `f = (stk, loc, C0, M0, pc)` sees
	  have tall: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock] \<or> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
	    by(auto simp add: split_beta split: split_if_asm)
	  thus ?thesis
	  proof(rule disjE)
	    assume tal: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock, Lock]"
	    with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
	    have "xs = [] \<and> L = Unlock \<and> ys = [Lock] \<or>
  	          xs = [Unlock] \<and> L = Lock \<and> ys = []"
	      by(auto simp add: neq_Nil_conv append_eq_Cons_conv Cons_eq_append_conv)
	    moreover
	    { assume [simp]: "xs = []" "L = Unlock" "ys = [Lock]"
	      from Invoke M tal `check P (None, h, f # Frs)` sees `f = (stk, loc, C0, M0, pc)` exec
	      have "\<exists>\<sigma>'. (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>, \<sigma>') \<in> set (exec (P, (None, h, f # Frs)))"
		by(auto split: split_if_asm)
	      then obtain xcp'' m'' frs''
		where "(\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>, xcp'', m'', frs'') \<in> set (exec (P, None, h, f # Frs))"
		by(clarsimp simp only: split_paired_Ex)
	      with `check P (None, h, f # Frs)`
	      have "P \<turnstile> Normal (None, h, f # Frs) -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>-jvmd\<rightarrow> Normal (xcp'', m'', frs'')"
		by(fastsimp intro: exec_1_d_NormalI simp add: exec_d_def)
	      moreover have "thread_oks ts m' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>t\<^esub>" by simp
	      moreover from `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
	      have "\<not> has_lock (ls l) t" by(simp)
	      hence "lock_ok_las' ls t \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub>"
		by(auto simp add: lock_ok_las'_def lock_actions_ok'_def)
	      moreover have "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> {}"
		by(auto elim!: collect_locks'E split: split_if_asm)
	      hence "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
	      ultimately have ?thesis using `x = (xcp, frs)` `frs = f # Frs`
		`f = (stk, loc, C0, M0, pc)` `check P (None, h, f # Frs)`
		`P \<turnstile> C0 sees M0: Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0` `xcp = None`
		by(fastsimp) }
	    moreover
	    { assume xsL: "xs = [Unlock] \<and> L = Lock \<and> ys = []"
	      then obtain [simp]: "xs = [Unlock]" "L = Lock" "ys = []" by auto
	      with `lock_actions_ok (ls l) t xs` `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
	      have "may_lock (upd_locks (ls l) t xs) t"
		unfolding `L = Lock` by-(rule ml)
	      with `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
	      have False by(auto) }
	    ultimately show ?thesis by blast
	  next
	    assume tal: "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
	    with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
	    have [simp]: "xs = []" "L = UnlockFail" "ys = []"
	      by(auto simp add: append_eq_Cons_conv Cons_eq_append_conv)
	    let ?ta' = "\<epsilon>\<lbrace>\<^bsub>w\<^esub> if M = notify then Notify l else NotifyAll l\<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>l, Lock\<rightarrow>l\<rbrace>"
	    from Invoke tal M `check P (None, h, f # Frs)` sees `f = (stk, loc, C0, M0, pc)` exec
	    have "(?ta', None, h, (Unit # tl stk, loc, C0, M0, pc+1) # Frs) \<in> set (exec (P, (None, h, f # Frs)))"
	      by(auto split: split_if_asm)
	    with `check P (None, h, f # Frs)`
	    have "P \<turnstile> Normal (None, h, f # Frs) -?ta'-jvmd\<rightarrow> Normal (None, h, (Unit # tl stk, loc, C0, M0, pc+1) # Frs)"
	      by(fastsimp intro: exec_1_d_NormalI simp add: exec_d_def)
	    moreover have "thread_oks ts m' \<lbrace>?ta'\<rbrace>\<^bsub>t\<^esub>" by simp
	    moreover from `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
	    have "has_lock (ls l) t" by simp
	    hence "lock_ok_las' ls t \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub>"
	      by(auto simp add: lock_ok_las'_def lock_actions_ok'_def
                      intro!: may_lock_t_may_lock_unlock_lock_t intro: has_lock_may_lock)
	    moreover have "collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> {}"
	      by(auto elim!: collect_locks'E split: split_if_asm)
	    hence "collect_locks' \<lbrace>?ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
	    ultimately show ?thesis using `x = (xcp, frs)` `frs = f # Frs`
	      `f = (stk, loc, C0, M0, pc)` `check P (None, h, f # Frs)`
	      `P \<turnstile> C0 sees M0: Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0` `xcp = None`
	      by(fastsimp)
	  qed
	qed
      next
	case MEnter
	with exec `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys` `f = (stk, loc, C0, M0, pc)` sees
	have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Lock]" by(auto simp add: split_beta split: split_if_asm)
	moreover with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
	have "xs = []" "ys = []" "L = Lock"
	  by(auto simp add: append_eq_Cons_conv Cons_eq_append_conv)
	with `lock_actions_ok (ls l) t xs` `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
	have "may_lock (upd_locks (ls l) t xs) t"
	  by-(rule ml, auto)
	with `\<not> lock_action_ok (upd_locks (ls l) t xs) t L` `L = Lock`
	have False by auto
	thus ?thesis by blast
      next
	case MExit
	with exec `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys` `f = (stk, loc, C0, M0, pc)` sees
	have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock] \<or> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]"
	  by(auto simp add: split_beta split: split_if_asm)
	with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys`
	have "L = Unlock \<or> L = UnlockFail" "xs = []" "ys = []"
	  by(auto simp add: append_eq_Cons_conv)
	from `L = Unlock \<or> L = UnlockFail` show ?thesis
	proof(rule disjE)
	  assume "L = Unlock"
	  with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys` `xs = []` `ys = []`
	  have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock]" by simp
	  moreover
	  from MExit `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [Unlock]` `check P (None, h, f # Frs)` sees `f = (stk, loc, C0, M0, pc)` exec
	  have "the_Addr (hd stk) = l"
	    by(auto simp add: is_Ref_def check_def split: split_if_asm)
	  moreover
	  note MExit exec `L = Unlock` `f = (stk, loc, C0, M0, pc)` sees
	  ultimately have "\<exists>\<sigma>'. (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>, \<sigma>') \<in> set (exec (P, (None, h, f # Frs)))"
	    by(auto split: split_if_asm simp del: split_paired_Ex)
	  then obtain xcp'' m'' frs''
	    where "(\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>, xcp'', m'', frs'') \<in> set (exec (P, None, h, f # Frs))"
	    by(clarsimp simp only: split_paired_Ex)
	  with `check P (None, h, f # Frs)`
	  have "P \<turnstile> Normal (None, h, f # Frs) -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>-jvmd\<rightarrow> Normal (xcp'', m'', frs'')"
	    by(fastsimp intro: exec_1_d_NormalI simp add: exec_d_def)
	  moreover have "thread_oks ts m' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>t\<^esub>" by simp
	  moreover from `xs = []` `L = Unlock` `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
	  have "\<not> has_lock (ls l) t" by(auto)
	  hence "lock_ok_las' ls t \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub>"
	    by(auto simp add: lock_ok_las'_def lock_actions_ok'_def)
	  moreover have "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> {}"
	    by(auto elim!: collect_locks'E split: split_if_asm)
	  hence "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
	  ultimately show ?thesis using `x = (xcp, frs)` `frs = f # Frs`
	    `f = (stk, loc, C0, M0, pc)` `check P (None, h, f # Frs)`
	    `P \<turnstile> C0 sees M0: Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0` `xcp = None`
	    by(fastsimp)
	next
	  assume "L = UnlockFail"
	  with `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = xs @ L # ys` `xs = []` `ys = []`
	  have "\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]" by simp
	  moreover
	  from MExit `\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l = [UnlockFail]` `check P (None, h, f # Frs)`
	    sees `f = (stk, loc, C0, M0, pc)` exec
	  have "the_Addr (hd stk) = l"
	    by(auto simp add: is_Ref_def check_def split: split_if_asm)
	  moreover
	  note MExit exec `L = UnlockFail` `f = (stk, loc, C0, M0, pc)` sees
	  ultimately have "\<exists>\<sigma>'. (\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l\<rbrace>, \<sigma>') \<in> set (exec (P, (None, h, f # Frs)))"
	    by(auto split: split_if_asm simp del: split_paired_Ex)
	  then obtain xcp'' m'' frs'' tls''
	    where "(\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l\<rbrace>, xcp'', m'', frs'') \<in> set (exec (P, None, h, f # Frs))"
	    by(clarsimp simp only: split_paired_Ex)
	  with `check P (None, h, f # Frs)`
	  have "P \<turnstile> Normal (None, h, f # Frs) -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l\<rbrace>-jvmd\<rightarrow> Normal (xcp'', m'', frs'')"
	    by(fastsimp intro: exec_1_d_NormalI simp add: exec_d_def)
	  moreover have "thread_oks ts m' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>t\<^esub>" by simp
	  moreover from `xs = []` `L = UnlockFail` `\<not> lock_action_ok (upd_locks (ls l) t xs) t L`
	  have "has_lock (ls l) t" by(auto)
	  hence "lock_ok_las' ls t \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub>"
	    by(auto simp add: lock_ok_las'_def lock_actions_ok'_def)
	  moreover have "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> {}"
	    by(auto elim!: collect_locks'E split: split_if_asm)
	  hence "collect_locks' \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
	  ultimately show ?thesis using `x = (xcp, frs)` `frs = f # Frs`
	    `f = (stk, loc, C0, M0, pc)` `check P (None, h, f # Frs)`
	    `P \<turnstile> C0 sees M0: Ts\<rightarrow>T = (mxs, mxl\<^isub>0, ins, xt) in C0` `xcp = None`
	    by(fastsimp)
	qed
      qed(fastsimp simp add: split_beta Cons_eq_append_conv split: split_if_asm)+
    qed
  qed
  thus "\<exists>ta' x' m'. mexecd P (x, shr s) ta' (x', m') \<and>
                    thread_oks (thr s) m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and>
                    lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and>
                    collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
                    final_thread.cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and>
                    final_thread.collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> final_thread.collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    by simp
qed


lemma mexecT_eq_mexecdT:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and cs: "correct_state_ts P \<Phi> (thr s) (shr s)"
  shows "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s' = P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
proof(rule iffI)
  assume "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'"
  thus "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  proof(induct rule: multithreaded.redT_elims[consumes 1, case_names normal acquire])
    case (normal x x')
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` cs
    have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from mexec_eq_mexecd[OF wf `P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>`] `mexec P (x, shr s) ta (x', shr s')`
    have "mexecd P (x, shr s) ta (x', shr s')" by simp
    with normal show ?case 
      apply -
      apply(rule multithreaded.redT_normal, assumption+)
      by(cases s', auto)
  next
    case acquire thus ?case
      apply(clarify)
      apply(rule multithreaded.redT_acquire, assumption+)
      by(cases s', auto)
  qed
next
  assume "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  thus "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'"
  proof(induct rule: multithreaded.redT_elims[consumes 1, case_names normal acquire])
    case (normal x x')
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` cs
    have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from mexec_eq_mexecd[OF wf `P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>`] `mexecd P (x, shr s) ta (x', shr s')`
    have "mexec P (x, shr s) ta (x', shr s')" by simp
    with normal show ?case 
      apply -
      apply(rule multithreaded.redT_normal, assumption+)
      by(cases s', auto)
  next
    case acquire thus ?case
      apply(clarify)
      apply(rule multithreaded.redT_acquire, assumption+)
      by(cases s', auto)
  qed
qed

lemma mExecT_eq_mExecdT:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and ct: "correct_state_ts P \<Phi> (thr s) (shr s)"
  shows "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s' = P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
proof
  assume Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  thus "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'" using ct
  proof(induct rule: multithreaded.RedT_induct[consumes 1, case_names refl step])
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
      by(blast intro: multithreaded.RedTI stepify_pred_step elim: multithreaded.RedTE)
  qed
next
  assume Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  thus "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'" using ct
  proof(induct rule: multithreaded.RedT_induct[consumes 1, case_names refl step])
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
      by(blast intro: multithreaded.RedTI stepify_pred_step elim: multithreaded.RedTE)
  qed
qed

lemma mexecT_preserves_thread_conf: 
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr s) (shr s); P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'; thread_conf P (thr s) (shr s) \<rbrakk> \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(simp only: mexecT_eq_mexecdT)(rule mexecdT_preserves_thread_conf)

lemma mExecT_preserves_thread_conf: 
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr s) (shr s); P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s'; thread_conf P (thr s) (shr s) \<rbrakk> \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(simp only: mExecT_eq_mExecdT)(rule mExecdT_preserves_thread_conf)

lemma exec_wf_red:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and csS: "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "wf_red final (mexec P) S"
proof
  fix tta s t x ta x' m'
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s"
    and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and "mexec P (x, shr s) ta (x', m')"
  moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
  moreover obtain xcp frs m where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have "ts t = \<lfloor>((xcp, frs), no_wait_locks)\<rfloor>" "mexec P ((xcp, frs), h) ta (x', m')" by auto
  from wf `correct_state_ts P \<Phi> (thr S) (shr S)` have "wf_red final (mexecd P) S" by(rule execd_wf_red)
  moreover from Red `correct_state_ts P \<Phi> (thr S) (shr S)` have css: "correct_state_ts P \<Phi> (thr s) (shr s)"
    by(auto dest: preserves_correct_state[OF wf])
  with `ts t = \<lfloor>((xcp, frs), no_wait_locks)\<rfloor>` have "P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>"
    by(auto dest: ts_okD)
  from `mexec P (x, shr s) ta (x', m')` have "mexecd P (x, shr s) ta (x', m')"
    by(simp add: mexec_eq_mexecd[OF wf `P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>`, simplified])
  moreover from Red have "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s" by(unfold mExecT_eq_mExecdT[OF wf csS])
  ultimately have "\<exists>ta' x' m'. mexecd P (x, shr s) ta' (x', m') \<and> thread_oks (thr s) m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and>
                            lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
                            final_thread.cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and>
                            final_thread.collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> final_thread.collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    using Red by-(rule wf_red.wf_red)
  then obtain ta' x' m'
    where "mexecd P (x, shr s) ta' (x', m')"
    and ta': "thread_oks (thr s) m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>" "lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>"
             "collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "final_thread.cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>"
             "final_thread.collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> final_thread.collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    by blast
  from `mexecd P (x, shr s) ta' (x', m')` have "mexec P (x, shr s) ta' (x', m')"
    by(simp add: mexec_eq_mexecd[OF wf `P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>`, simplified])
  with ta'
  show "\<exists>ta' x' m'.
             mexec P (x, shr s) ta' (x', m') \<and>
             thread_oks (thr s) m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and>
             lock_ok_las' (locks s) t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and>
             collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
             final_thread.cond_action_oks' s t \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and>
             exec_mthr.collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>
             \<subseteq> exec_mthr.collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" 
    by(blast)
qed


lemma execd_wf_progress:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "wf_progress final (mexecd P) S"
proof
  fix tta s t x ln
  assume "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "\<not> final x"
    and Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
  moreover obtain ls ts h ws where s [simp]: "s = (ls, (ts, h), ws)" by(cases s, auto)
  ultimately have "ts t = \<lfloor>(x, ln)\<rfloor>" by simp
  from Red `correct_state_ts P \<Phi> (thr S) (shr S)`
  have "correct_state_ts P \<Phi> ts h"
    by(auto dest: preserves_correct_state_d[OF wf])
  obtain xcp frs where "x = (xcp, frs)" by (cases x, auto)
  with `\<not> final x` obtain f Frs where "frs = f # Frs"
    by(fastsimp simp add: neq_Nil_conv)
  with `ts t = \<lfloor>(x, ln)\<rfloor>` `correct_state_ts P \<Phi> ts h` `x = (xcp, frs)`
  have "P,\<Phi> \<turnstile> (xcp, h, f # Frs) \<surd>" by(auto dest: ts_okD)
  hence "xcp = None" by(auto simp add: correct_state_def)
  with `wf_jvm_prog\<^sub>\<Phi> P` `P,\<Phi> \<turnstile> (xcp, h, f # Frs) \<surd>` 
  have "exec_d P (None, h, f # Frs) \<noteq> TypeError" by(auto dest: no_type_error)
  then obtain \<Sigma> where "exec_d P (None, h, f # Frs) = Normal \<Sigma>" by(auto)
  hence "exec (P, None, h, f # Frs) = \<Sigma>"
    by(auto simp add: exec_d_def check_def split: split_if_asm)
  hence "\<Sigma> \<noteq> []"
    by -(drule sym, auto intro: exec_not_empty del: notI)
  then obtain ta \<sigma> where "(ta, \<sigma>) \<in> set \<Sigma>" by(fastsimp simp add: neq_Nil_conv)
  with `x = (xcp, frs)` `frs = f # Frs` `P,\<Phi> \<turnstile> (xcp, h, f # Frs) \<surd>`
    `wf_jvm_prog\<^sub>\<Phi> P` `exec_d P (None, h, f # Frs) = Normal \<Sigma>` `xcp = None`
  show "\<exists>ta x' m'. mexecd P (x, shr s) ta (x', m')"
    by(cases ta, cases \<sigma>)(fastsimp simp add: split_paired_Ex intro: exec_1_d_NormalI)
qed

lemma exec_wf_progress:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P" 
  and cs: "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "wf_progress final (mexec P) S"
proof
  fix tta s t x ln
  assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "\<not> final x"
    and Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s"
  obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  with `\<not> final x` obtain f Frs where [simp]: "frs = f # Frs"
    by(fastsimp simp add: neq_Nil_conv)
  from cs Red have "correct_state_ts P \<Phi> (thr s) (shr s)"
    by(auto dest: preserves_correct_state[OF wf])
  with `thr s t = \<lfloor>(x, ln)\<rfloor>` have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
  hence [simp]: "xcp = None" by(auto simp add: correct_state_def)
  with exec_not_empty[where P=P and h="shr s" and f=f and frs=Frs]
  show "\<exists>ta x' m'. mexec P (x, shr s) ta (x', m')"
    by(fastsimp simp add: split_paired_Ex exec_1_iff neq_Nil_conv)
qed


lemma progress_deadlock:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr S) (shr S);
     lock_thread_ok (locks S) (thr S) \<rbrakk> 
  \<Longrightarrow> progress final (mexec P) S (final_thread_wf.deadlock final (mexec P))"
apply(rule final_thread_wf.progress_deadlock[OF final_interp])
apply(rule exec_wf_progress, assumption+)
apply(rule exec_wf_red, assumption+)
apply(unfold_locales, rule multithreaded.RedT_preserves_lock_thread_ok, assumption+)
done

lemma progress_deadlocked:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr S) (shr S);
     lock_thread_ok (locks S) (thr S) \<rbrakk> 
  \<Longrightarrow> progress final (mexec P) S (final_thread_wf.deadlocked' final (mexec P))"
apply(rule final_thread_wf.progress_deadlocked'[OF final_interp])
apply(rule exec_wf_progress, assumption+)
apply(rule exec_wf_red, assumption+)
apply(unfold_locales, rule multithreaded.RedT_preserves_lock_thread_ok, assumption+)
done

lemma progress_deadlock_d:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr S) (shr S);
     lock_thread_ok (locks S) (thr S) \<rbrakk> 
  \<Longrightarrow> progress final (mexecd P) S (final_thread_wf.deadlock final (mexecd P))"
apply(rule final_thread_wf.progress_deadlock[OF final_interp_d])
apply(rule execd_wf_progress, assumption+)
apply(rule execd_wf_red, assumption+)
apply(unfold_locales, rule multithreaded.RedT_preserves_lock_thread_ok, assumption+)
done

lemma progress_deadlocked_d:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; correct_state_ts P \<Phi> (thr S) (shr S);
     lock_thread_ok (locks S) (thr S) \<rbrakk> 
  \<Longrightarrow> progress final (mexecd P) S (final_thread_wf.deadlocked' final (mexecd P))"
apply(rule final_thread_wf.progress_deadlocked'[OF final_interp_d])
apply(rule execd_wf_progress, assumption+)
apply(rule execd_wf_red, assumption+)
apply(unfold_locales, rule multithreaded.RedT_preserves_lock_thread_ok, assumption+)
done


theorem mexecd_TypeSafety:
  fixes ln :: "addr \<Rightarrow> nat"
  assumes "wf_jvm_prog\<^sub>\<Phi> P"
  and "correct_state_ts P \<Phi> (thr s) (shr s)"
  and "lock_thread_ok (locks s) (thr s)"
  and "thread_conf P (thr s) (shr s)"
  and "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  and "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'')"
  and "thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>"
  shows "thread_conf P (thr s') (shr s') \<and> (frs \<noteq> [] \<longrightarrow> xcp = None) \<and> (frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<longrightarrow> execd_mthr_final.deadlocked P s' t) \<and> P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>"
proof(rule conjI)
  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'` `thread_conf P (thr s) (shr s)`
  show "thread_conf P (thr s') (shr s')"
    by-(rule mExecdT_preserves_thread_conf)
next
  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
  have "correct_state_ts P \<Phi> (thr s') (shr s')"
    by(fastsimp dest: lifting_wf.RedT_preserves[OF lifting_wf_correct_state_d])
  from `lock_thread_ok (locks s) (thr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'`
  have "lock_thread_ok (locks s') (thr s')"
    by(fastsimp intro: multithreaded.RedT_preserves_lock_thread_ok)
  from `correct_state_ts P \<Phi> (thr s') (shr s')`
    `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>`
  have cst: "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>" by(auto dest: ts_okD)
  show "(frs \<noteq> [] \<longrightarrow> xcp = None) \<and> (frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<longrightarrow> final_thread_wf.deadlocked final (mexecd P) s' t) \<and> P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>"
  proof(rule conjI[OF impI conjI[OF impI]])
    assume "frs \<noteq> []"
    then obtain f Frs where "frs = f # Frs"
      by(cases s', fastsimp simp add: neq_Nil_conv)
    with cst show "xcp = None" by(simp add: correct_state_def)
  next
    assume "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks"
    with `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>` have "execd_mthr_final.not_final_thread s' t"
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
  next
    from cst show  "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>" .
  qed
qed


theorem mexec_TypeSafety:
  fixes ln :: "addr \<Rightarrow> nat"
  assumes "wf_jvm_prog\<^sub>\<Phi> P"
  and "correct_state_ts P \<Phi> (thr s) (shr s)"
  and "lock_thread_ok (locks s) (thr s)"
  and "thread_conf P (thr s) (shr s)"
  and "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  and "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'')"
  and "thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>"
  shows "thread_conf P (thr s') (shr s') \<and> (frs \<noteq> [] \<longrightarrow> xcp = None) \<and> (frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<longrightarrow> exec_mthr_final.deadlocked P s' t) \<and> P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>"
proof(rule conjI)
  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'` `thread_conf P (thr s) (shr s)`
  show "thread_conf P (thr s') (shr s')"
    by-(rule mExecT_preserves_thread_conf)
next
  from `wf_jvm_prog\<^sub>\<Phi> P` `correct_state_ts P \<Phi> (thr s) (shr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
  have "correct_state_ts P \<Phi> (thr s') (shr s')"
    by(fastsimp elim: lifting_wf.RedT_preserves[OF lifting_wf_correct_state])
  from `lock_thread_ok (locks s) (thr s)` `P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'`
  have "lock_thread_ok (locks s') (thr s')"
    by(fastsimp intro: multithreaded.RedT_preserves_lock_thread_ok)
  from `correct_state_ts P \<Phi> (thr s') (shr s')`
    `thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>`
  have cst: "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>" by(auto dest: ts_okD)
  show "(frs \<noteq> [] \<longrightarrow> xcp = None) \<and> (frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<longrightarrow> final_thread_wf.deadlocked final (mexec P) s' t) \<and> P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>"
  proof(rule conjI[OF impI conjI[OF impI]])
    assume "frs \<noteq> []"
    then obtain f Frs where "frs = f # Frs"
      by(cases s', fastsimp simp add: neq_Nil_conv)
    with cst show "xcp = None" by(simp add: correct_state_def)
  next
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
  next
    from cst show "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>" .
  qed
qed

end
