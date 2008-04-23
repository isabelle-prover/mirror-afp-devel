(*  Title:      JinjaThreads/BV/JVMDeadlocked.thy
    Author:     Andreas Lochbihler
*)

theory JVMDeadlocked imports BVProgressThreaded begin

lemma must_lock_implies_MEnter:
  assumes ml: "P \<turnstile> \<langle>(None, h, f # Frs)\<rangle>\<^isub>d \<wrong>" 
  and cs: "P,\<Phi> \<turnstile> (None, h, f # Frs) \<surd>"
  and wf: "wf_jvm_prog\<^sub>\<Phi> P"
  shows "\<exists>stk loc C M pc. f = (stk, loc, C, M, pc) \<and> (instrs_of P C M ! pc = MEnter \<and> hd stk \<noteq> Null \<or>
                                                      instrs_of P C M ! pc = Invoke join 0 \<and>
                                                       (\<exists>a C' fs. stk ! 0 = Addr a \<and> h a = \<lfloor>Obj C' fs\<rfloor> \<and> P \<turnstile> C' \<preceq>\<^sup>* Thread))"
proof-
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)
  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "P \<turnstile> h \<surd>" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs"
    by (fastsimp simp add: correct_state_def dest: sees_method_fun)

  from wf cs have "exec_d P (None, h, f # Frs) \<noteq> TypeError"
    by(auto dest: no_type_error)
  then obtain \<Sigma> where "exec_d P (None, h, f # Frs) = Normal \<Sigma>" by(auto)
  hence sigma: "exec (P, None, h, f # Frs) = \<Sigma>"
    by(auto simp add: exec_d_def check_def split: split_if_asm)
  hence "\<Sigma> \<noteq> []"
    by-(drule sym,clarify del: notI,rule exec_not_empty)
  then obtain ta \<sigma> where "(ta, \<sigma>) \<in> set \<Sigma>" by(fastsimp simp add: neq_Nil_conv)
  with `exec_d P (None, h, f # Frs) = Normal \<Sigma>`
  have redd: "P \<turnstile> Normal (None, h, f # Frs) -ta-jvmd\<rightarrow> Normal \<sigma>"
    by -(rule exec_1_d.intros)
  with ml have "(\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
    by(cases \<sigma>)(erule multithreaded.must_syncD, auto)
  thus ?thesis
  proof(rule disjE)
    assume "\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
    then obtain l where l: "Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)" by blast
    with redd meth
    have "ins ! pc = MEnter \<or> ins ! pc = Invoke wait 0 \<or> ins ! pc = Invoke notify 0 \<or> ins ! pc = Invoke notifyAll 0"
      by(auto elim!: jvmd_NormalE, cases "ins ! pc",auto simp add: split_beta split: split_if_asm)
    moreover
    { assume [simp]: "ins ! pc = MEnter"
      with meth l `(ta, \<sigma>) \<in> set \<Sigma>` sigma[symmetric]
      have "hd stk \<noteq> Null" by(auto)
      with meth have ?thesis by(simp) }
    moreover
    { assume "ins ! pc = Invoke wait 0 \<or> ins ! pc = Invoke notify 0 \<or> ins ! pc = Invoke notifyAll 0"
      with meth `(ta, \<sigma>) \<in> set \<Sigma>` `exec (P, None, h, f # Frs) = \<Sigma>`[symmetric] l
      have "\<exists>\<sigma>'. (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>, \<sigma>') \<in> set (exec (P, None, h, f # Frs))"
	by(auto split: split_if_asm)
      then obtain \<sigma>' where "(\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>, \<sigma>') \<in> set (exec (P, None, h, f # Frs))" by blast
      with `exec_d P (None, h, f # Frs) = Normal \<Sigma>` sigma
      have "P \<turnstile> Normal (None, h, f # Frs) -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>-jvmd\<rightarrow> Normal \<sigma>'"
	by-(rule exec_1_d.intros,blast, simp)
      with ml have "\<exists>l'. Lock \<in> set (\<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub> l')"
	by(cases \<sigma>')(drule multithreaded.must_syncD[where ta="\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>"], auto)
      hence False by(auto split: split_if_asm) }
    ultimately show ?thesis by blast
  next
    assume "\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    then obtain t where t: "Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by blast
    with redd meth have [simp]: "ins ! pc = Invoke join 0"
      by(auto elim!: jvmd_NormalE, cases "ins ! pc",auto simp add: split_beta split: split_if_asm)
    moreover
    with meth `(ta, \<sigma>) \<in> set \<Sigma>` sigma[symmetric] t
    have "stk ! 0 \<noteq> Null" by(auto split: split_if_asm)
    moreover
    from `exec_d P (None, h, f # Frs) \<noteq> TypeError` have "check P (None, h, f # Frs)"
      by(auto simp add: exec_d_def split: split_if_asm)
    with `stk ! 0 \<noteq> Null` meth obtain a C' fs'
      where "stk ! 0 = Addr a"
      and "h a = \<lfloor>Obj C' fs'\<rfloor>"
      by(fastsimp simp add: check_def is_Ref_def neq_Nil_conv elim!: is_ArrE)
    moreover
    with meth `(ta, \<sigma>) \<in> set \<Sigma>` sigma[symmetric] t have "a = t" "P \<turnstile> Class C' \<le> Class Thread"
      by(auto simp add: split_beta split: split_if_asm)
    ultimately show ?thesis using meth by(simp)
  qed
qed

lemma join_hext:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and cs: "P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>"
  and red: "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
  and join: "Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
  and hext: "hext h h'"
  shows "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
proof -
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(blast dest: wt_jvm_progD)
  from red obtain f Frs
    where check: "check P (xcp, h, frs)" 
    and exec: "(ta, xcp', m', frs') \<in> set (exec (P, xcp, h, frs))" 
    and "(xcp, h, frs) = (None, h, f # Frs)"
    by(blast elim: jvmd_NormalE)
  hence [simp]: "xcp = None" "frs = f # Frs" by auto
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by(cases f, blast)
  from cs obtain Ts T mxs mxl0 ins xt ST LT 
    where "P \<turnstile> h \<surd>"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastsimp simp add: correct_state_def)
  from sees exec join have [simp]: "ins ! pc = Invoke join 0"
    by(cases "ins!pc")(fastsimp split: split_if_asm simp add: split_beta)+
  from check sees hext have "check P (xcp, h', frs)"
    by(auto simp add: check_def elim!: is_ArrE dest: hext_objD)
  moreover
  with sees have "stk \<noteq> []" "is_Ref (stk ! 0)"
    by(auto simp add: check_def)
  then obtain st Stk where [simp]: "stk = st # Stk" by(auto simp add: neq_Nil_conv)
  with `is_Ref (stk ! 0)` obtain a where "st = Null \<or> st = Addr a"
    by(auto simp add: is_Ref_def)
  from sees exec join have "st = Null \<Longrightarrow> False"
    by(auto simp add: split_beta split: split_if_asm)
  with `st = Null \<or> st = Addr a` have [simp]: "st = Addr a" by blast
  with check sees obtain D fs where [simp]: "h a = \<lfloor>Obj D fs\<rfloor>"
    by(fastsimp elim!: is_ArrE simp add: check_def)
  with hext obtain fs' where [simp]: "h' a = \<lfloor>Obj D fs'\<rfloor>"
    by(blast dest: hext_objD)
  from exec sees join
  have "(ta, xcp', h', frs') \<in> set (exec (P, xcp, h', frs))"
    by(simp add: split_beta split: split_if_asm)
  ultimately show ?thesis
    by -(rule exec_1_d_NormalI[where \<Sigma>="exec (P, xcp, h', frs)"], simp only: exec_d_def if_True)
qed  


lemma must_sync_preserved_d:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and ml: "P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d \<wrong>" 
  and hext: "hext h h'"
  and cs: "P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>"
  shows "P \<turnstile> \<langle>(xcp, h', frs)\<rangle>\<^isub>d \<wrong>"
proof(rule multithreaded.must_syncI)
  fix ta x' m'
  assume "mexecd P ((fst (xcp, h', frs), snd (snd (xcp, h', frs))), fst (snd (xcp, h', frs))) ta (x', m')"
  moreover obtain xcp' frs' where [simp]: "x' = (xcp', frs')" by(cases x', auto)
  ultimately have red: "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')" by simp
  then obtain f Frs
    where [simp]: "xcp = None"
    and check: "check P (xcp, h', frs)"
    and exec: "(ta, xcp', m', frs') \<in> set (exec (P, xcp, h', frs))"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)
  
  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "P \<turnstile> h \<surd>" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs"
    by (fastsimp simp add: correct_state_def dest: sees_method_fun)
  
  from ml cs meth have "ins ! pc = MEnter \<and> hd stk \<noteq> Null \<or> ins ! pc = Invoke join 0 \<and>
                                                       (\<exists>a C' fs. stk ! 0 = Addr a \<and> h a = \<lfloor>Obj C' fs\<rfloor> \<and> P \<turnstile> C' \<preceq>\<^sup>* Thread)"
    unfolding `xcp = None` `frs = f # Frs`
    by-(drule must_lock_implies_MEnter[OF _ _ wf], assumption, clarsimp)
  with red meth hext show "(\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
    by(auto elim!: jvmd_NormalE simp add: split_beta split: split_if_asm dest: hext_objD)
next
  from ml obtain ta xcp' frs' m'
    where red: "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    by -(erule  multithreaded.must_syncE, auto)
  with ml have lj: "(\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
    by -(erule multithreaded.must_syncD, auto)
  from red obtain f Frs
    where [simp]: "xcp = None"
    and check: "check P (xcp, h, frs)"
    and exec: "(ta, xcp', m', frs') \<in> set (exec (P, xcp, h, frs))"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)

  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "P \<turnstile> h \<surd>" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs"
    by (fastsimp simp add: correct_state_def dest: sees_method_fun)

  from lj have "\<exists>ta xcp' h'' frs'. P \<turnstile> Normal (None, h', (stk, loc, C, M, pc) # Frs) -ta-jvmd\<rightarrow> Normal (xcp', h'', frs')"
  proof(rule disjE)
    assume "\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
    then obtain l where l: "Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)" by blast
    with meth exec
    have "ins ! pc = MEnter \<or> ins ! pc = Invoke wait 0 \<or> ins ! pc = Invoke notify 0 \<or> ins ! pc = Invoke notifyAll 0"
      by(cases "ins ! pc")(auto simp add: split_beta split: split_if_asm)
    moreover
    { assume [simp]: "ins ! pc = MEnter"
      with meth l exec
      have "hd stk \<noteq> Null" by(auto)
      with check meth obtain a where [simp]: "hd stk = Addr a"
	by(auto elim: is_AddrE simp add: check_def is_Ref_def)
      from meth exec have "(ta, xcp', h', frs') \<in> set (exec (P, xcp, h', frs))" by(simp)
      moreover from meth check have "check P (xcp, h', frs)" by(simp add: check_def)
      ultimately have "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
	by -(rule exec_1_d_NormalI[where \<Sigma> = "exec (P, xcp, h', frs)"], simp add: exec_d_def)
      hence ?thesis by auto }
    moreover
    { assume M: "ins ! pc = Invoke wait 0 \<or> ins ! pc = Invoke notify 0 \<or> ins ! pc = Invoke notifyAll 0"
      with meth l exec
      have "stk ! 0 \<noteq> Null" "xcp' = None" by(auto split: split_if_asm)
      with M check meth obtain a where stk0: "stk ! 0 = Addr a" and lstk: "length stk > 0"
	by(auto elim!: is_AddrE simp add: check_def is_Ref_def)
      with frame obtain arrobj where "h a = \<lfloor>arrobj\<rfloor>"
	by(auto simp add: conf_f_def neq_Nil_conv list_all2_Cons1 conf_def)
      with hext obtain arrobj' where "h' a = \<lfloor>arrobj'\<rfloor>" by(auto dest: hext_objarrD)
      with stk0 lstk meth exec check M l `xcp' = None`
      have "(ta, xcp', h', frs') \<in> set (exec (P, xcp, h', frs))"
	by(cases "l = a", auto split: split_if_asm)
      moreover from meth check M stk0 `h' a = \<lfloor>arrobj'\<rfloor>`
      have "check P (xcp, h', frs)" by(auto simp add: check_def)
      ultimately have "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
	by -(rule exec_1_d_NormalI[where \<Sigma> = "exec (P, xcp, h', frs)"], simp add: exec_d_def)
      hence ?thesis by auto }
    ultimately show ?thesis by blast
  next
    assume "\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    then obtain t where t: "Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by blast
    from join_hext[OF wf cs red t hext] show ?thesis by auto
  qed
  thus "\<exists>ta x' m'. mexecd P ((fst (xcp, h', frs), snd (snd (xcp, h', frs))), fst (snd (xcp, h', frs))) ta (x', m')"
    by(fastsimp simp add: split_paired_Ex)
qed


lemma can_sync_devreserp_d:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and cl': "P \<turnstile> \<langle>(xcp, h', frs)\<rangle>\<^isub>d L \<wrong>" 
  and cs: "P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>"
  and Lnempty: "L \<noteq> {}"
  and hext: "hext h h'"
  shows "\<exists>L'\<subseteq>L. P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d L' \<wrong>"
proof -
  from cl' obtain ta xcp' frs' m'
    where red: "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and L: "L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
    by -(erule  multithreaded.can_syncE, auto)
  then obtain f Frs
    where [simp]: "xcp = None"
    and check: "check P (xcp, h', frs)"
    and exec: "(ta, xcp', m', frs') \<in> set (exec (P, xcp, h', frs))"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)
  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "P \<turnstile> h \<surd>" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs"
    by (fastsimp simp add: correct_state_def dest: sees_method_fun)

  from Lnempty L have "(\<exists>l. l \<in> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
    by(auto)
  thus ?thesis
  proof(rule disjE)
    assume "\<exists>l. l \<in> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    then obtain l where l: "l \<in> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by blast

    with meth exec
    have "ins ! pc = MEnter \<or> ins ! pc = Invoke wait 0 \<or> ins ! pc = Invoke notify 0 \<or> ins ! pc = Invoke notifyAll 0"
      by(cases "ins ! pc")(auto simp add: split_beta collect_locks_def split: split_if_asm)
    hence "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h, frs')"
    proof(rule disjE)
      assume [simp]: "ins ! pc = MEnter"
      with meth l exec L
      have "hd stk \<noteq> Null" by(auto simp add: collect_locks_def)
      with check meth obtain a where [simp]: "hd stk = Addr a"
	by(auto elim: is_AddrE simp add: check_def is_Ref_def) 
      from meth exec have "(ta, xcp', h, frs') \<in> set (exec (P, xcp, h, frs))" by(simp)
      moreover from meth check have "check P (xcp, h, frs)" by(simp add: check_def)
      ultimately show ?thesis
	by -(rule exec_1_d_NormalI[where \<Sigma> = "exec (P, xcp, h, frs)"], simp add: exec_d_def)
    next
      assume M: "ins ! pc = Invoke wait 0 \<or> ins ! pc = Invoke notify 0 \<or> ins ! pc = Invoke notifyAll 0"
      with meth l exec
      have "stk ! 0 \<noteq> Null" "xcp' = None" by(auto simp add: collect_locks_def split: split_if_asm)
      with M check meth obtain a where stk0: "stk ! 0 = Addr a" and lstk: "length stk > 0"
	by(auto elim!: is_AddrE simp add: check_def is_Ref_def)
      with frame obtain arrobj where "h a = \<lfloor>arrobj\<rfloor>"
	by(auto simp add: conf_f_def neq_Nil_conv list_all2_Cons1 conf_def)
      with stk0 lstk meth exec check M L l `xcp' = None`
      have "(ta, xcp', h, frs') \<in> set (exec (P, xcp, h, frs))"
	by(cases "l = a", auto split: split_if_asm simp add: collect_locks_def)
      moreover from meth check M stk0 `h a = \<lfloor>arrobj\<rfloor>`
      have "check P (xcp, h, frs)" by(auto simp add: check_def)
      ultimately show ?thesis
	by -(rule exec_1_d_NormalI[where \<Sigma> = "exec (P, xcp, h, frs)"], simp add: exec_d_def)
    qed
    hence "multithreaded.can_sync (mexecd P) (fst (xcp, h, frs), snd (snd (xcp, h, frs))) (fst (snd (xcp, h, frs))) L"
      by -(rule multithreaded.can_syncI[OF _ L],auto)
    thus ?thesis by blast
  next
    assume "\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    then obtain t where t: "Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by blast
    with meth exec have [simp]: "ins ! pc = Invoke join 0"
      by(cases "ins!pc")(fastsimp split: split_if_asm simp add: split_beta)+
    with meth t exec
    have "stk ! 0 \<noteq> Null" "xcp' = None"
      by(auto split: split_if_asm simp add: split_beta)
    with check meth obtain a where stk0: "stk ! 0 = Addr a" and lstk: "length stk > 0"
      by(auto elim!: is_AddrE simp add: check_def is_Ref_def)
    with frame obtain arrobj where ha: "h a = \<lfloor>arrobj\<rfloor>"
      by(auto simp add: conf_f_def neq_Nil_conv list_all2_Cons1 conf_def)
    from check meth stk0 obtain D fs' where h'a: "h' a = \<lfloor>Obj D fs'\<rfloor>" 
      by(fastsimp simp add: check_def elim!: is_ArrE)
    with ha hext have "\<exists>fs. h a = \<lfloor>Obj D fs\<rfloor>"
      by(cases arrobj, auto dest: hext_objD hext_arrD)
    then obtain fs where [simp]: "h a = \<lfloor>Obj D fs\<rfloor>" by blast
    from h'a t exec meth stk0 have DThread: "P \<turnstile> D \<preceq>\<^sup>* Thread"
      by(auto simp add: split_beta split: split_if_asm)
    with stk0 check meth h'a have "check P (xcp, h, frs)"
      by(auto simp add: check_def)
    moreover from meth exec stk0 h'a DThread t
    have "(ta, xcp', h, frs') \<in> set (exec (P, xcp, h, frs))"
      by(auto)
    ultimately have "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h, frs')"
      by -(rule exec_1_d_NormalI, simp only: exec_d_def if_True)
    with L have "multithreaded.can_sync (mexecd P) (xcp, frs) h L"
      by(auto intro: multithreaded.can_syncI)
    thus ?thesis by(auto)
  qed
qed


lemma execd_preserve_deadlocked:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and cs: "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "preserve_deadlocked final (mexecd P) S"
proof(unfold_locales)
  fix tta s t' ta' s' t x ln
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "multithreaded.must_sync (mexecd P) x (shr s)"
  moreover obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have ml: "P \<turnstile> \<langle>(xcp, shr s, frs)\<rangle>\<^isub>d \<wrong>" by auto
  moreover from cs Red have cs': "correct_state_ts P \<Phi> (thr s) (shr s)"
    by-(rule preserves_correct_state_d[OF wf])
  with tst have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>"
    by(auto dest: ts_okD)
  moreover from red have "hext (shr s) (shr s')"
    by(rule execd_hext)
  ultimately have "P \<turnstile> \<langle>(xcp, shr s', frs)\<rangle>\<^isub>d \<wrong>"
    by-(rule must_sync_preserved_d[OF wf])
  thus "multithreaded.must_sync (mexecd P) x (shr s')" by simp
next
  fix tta s t' ta' s' t x ln L
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "multithreaded.can_sync (mexecd P) x (shr s') L"
    and L: "L \<noteq> {}"
  moreover obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have ml: "P \<turnstile> \<langle>(xcp, shr s', frs)\<rangle>\<^isub>d L \<wrong>" by auto
  moreover from cs Red have cs': "correct_state_ts P \<Phi> (thr s) (shr s)"
    by-(rule preserves_correct_state_d[OF wf])
  with tst have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>"
    by(auto dest: ts_okD)
  moreover from red have "hext (shr s) (shr s')"
    by(rule execd_hext)
  ultimately have "\<exists>L' \<subseteq> L. P \<turnstile> \<langle>(xcp, shr s, frs)\<rangle>\<^isub>d L' \<wrong>"
    using L by-(rule can_sync_devreserp_d[OF wf])
  thus "\<exists>L' \<subseteq> L. multithreaded.can_sync (mexecd P) x (shr s) L'" by simp
qed


text {* and now everything again for the aggresive VM *}

lemma must_lock_d_eq_must_lock:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,\<Phi> \<turnstile> (xcp, h, frs) \<surd> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d \<wrong> = P \<turnstile> \<langle>(xcp, h, frs)\<rangle> \<wrong>"
apply(simp)
apply(rule iffI)
 apply(rule multithreaded.must_syncI)
  apply(erule multithreaded.must_syncD)
  apply(simp only: mexec_eq_mexecd)
 apply(erule multithreaded.must_syncE)
 apply(simp only: mexec_eq_mexecd)
 apply(blast)
apply(rule multithreaded.must_syncI)
 apply(erule multithreaded.must_syncD)
 apply(simp only: mexec_eq_mexecd[symmetric])
apply(erule multithreaded.must_syncE)
apply(simp only: mexec_eq_mexecd[symmetric])
apply(blast)
done

lemma can_lock_d_eq_can_lock:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,\<Phi> \<turnstile> (xcp, h, frs) \<surd> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d L \<wrong> = P \<turnstile> \<langle>(xcp, h, frs)\<rangle> L \<wrong>"
apply(simp)
apply(rule iffI)
 apply(erule multithreaded.can_syncE)
 apply(rule multithreaded.can_syncI)
   apply(simp only: mexec_eq_mexecd)
  apply(assumption)+
apply(erule multithreaded.can_syncE)
apply(rule multithreaded.can_syncI)
 by(simp only: mexec_eq_mexecd)

lemma exec_preserve_deadlocked:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and cs: "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "preserve_deadlocked final (mexec P) S"
proof -
  { fix tta s t' ta' s' t x ln
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s"
      and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvm\<^esub> s'"
      and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from wf cs Red have Redd: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
      by(simp add: mExecT_eq_mExecdT)
    moreover from Red cs have css: "correct_state_ts P \<Phi> (thr s) (shr s)" 
      by-(rule preserves_correct_state[OF wf])
    with red have redd: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
      by(simp add: mexecT_eq_mexecdT[OF wf])
    from css tst have cst: "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from redd have cst': "P,\<Phi> \<turnstile> (xcp, shr s', frs) \<surd>"
    proof(induct rule: multithreaded.redT_elims[consumes 1, case_names normal acquire])
      case acquire with cst show ?case by simp
    next
      case (normal X X')
      obtain XCP FRS where X [simp]: "X = (XCP, FRS)" by(cases X, auto)
      obtain XCP' FRS' where X' [simp]: "X' = (XCP', FRS')" by(cases X', auto)
      from `mexecd P (X, shr s) ta' (X', shr s')`
      have "P \<turnstile> Normal (XCP, shr s, FRS) -ta'-jvmd\<rightarrow> Normal (XCP', shr s', FRS')" by simp
      moreover from `thr s t' = \<lfloor>(X, no_wait_locks)\<rfloor>` css
      have "P,\<Phi> \<turnstile> (XCP, shr s, FRS) \<surd>" by(auto dest: ts_okD)
      ultimately show ?case using `P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>` by -(rule correct_state_heap_change[OF wf])
    qed
    { assume "multithreaded.must_sync (mexec P) x (shr s)"
      hence ml: "P \<turnstile> \<langle>(xcp, shr s, frs)\<rangle> \<wrong>" by simp
      with cst have "P \<turnstile> \<langle>(xcp, shr s, frs)\<rangle>\<^isub>d \<wrong>"
	by(auto dest: must_lock_d_eq_must_lock[OF wf])
      with Redd redd tst have "multithreaded.must_sync (mexecd P) x (shr s')"
	by(auto elim!: preserve_lock_behav.must_lock_preserved[OF preserve_deadlocked.axioms(2)[OF execd_preserve_deadlocked[OF wf cs]]])
      with cst' have "multithreaded.must_sync (mexec P) x (shr s')"
	by(auto dest: must_lock_d_eq_must_lock[OF wf]) }
    note ml = this
    { fix L
      assume "multithreaded.can_sync (mexec P) x (shr s') L"
	and L: "L \<noteq> {}"
      hence cl: "P \<turnstile> \<langle>(xcp, shr s', frs)\<rangle> L \<wrong>" by simp
      with cst' have "P \<turnstile> \<langle>(xcp, shr s', frs)\<rangle>\<^isub>d L \<wrong>"
	by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with Redd redd tst L
      have "\<exists>L' \<subseteq> L. multithreaded.can_sync (mexecd P) x (shr s) L'"
	by -(rule preserve_lock_behav.can_lock_devreserp[OF preserve_deadlocked.axioms(2)[OF execd_preserve_deadlocked[OF wf cs]]], auto)
      then obtain L' where "multithreaded.can_sync (mexecd P) x (shr s) L'" 
	and L': "L'\<subseteq> L" by blast
      with cst have "multithreaded.can_sync (mexec P) x (shr s) L'"
	by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with L' have "\<exists>L' \<subseteq> L. multithreaded.can_sync (mexec P) x (shr s) L'"
	by(blast) }
    note this ml }
  thus ?thesis by(unfold_locales)
qed


end
