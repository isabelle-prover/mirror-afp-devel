(*  Title:      JinjaThreads/BV/BVSpecTypeSafe.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{BV Type Safety Proof}\label{sec:BVSpecTypeSafe} *}

theory BVSpecTypeSafe
imports BVConform
begin

text {*
  This theory contains proof that the specification of the bytecode
  verifier only admits type safe programs.  
*}

section {* Preliminaries *}

text {*
  Simp and intro setup for the type safety proof:
*}
lemmas defs1 = correct_state_def conf_f_def wt_instr_def eff_def norm_eff_def app_def xcpt_app_def

lemmas widen_rules [intro] = conf_widen confT_widen confs_widens confTs_widen

  
section {* Exception Handling *}


text {*
  For the @{text Invoke} instruction the BV has checked all handlers
  that guard the current @{text pc}.
*}
lemma Invoke_handlers:
  "match_ex_table P C pc xt = Some (pc',d') \<Longrightarrow> 
  \<exists>(f,t,D,h,d) \<in> set (relevant_entries P (Invoke n M) pc xt). 
   P \<turnstile> C \<preceq>\<^sup>* D \<and> pc \<in> {f..<t} \<and> pc' = h \<and> d' = d"
  by (induct xt) (auto simp add: relevant_entries_def matches_ex_entry_def 
                                 is_relevant_entry_def split: split_if_asm)


text {*
  We can prove separately that the recursive search for exception
  handlers (@{text find_handler}) in the frame stack results in 
  a conforming state (if there was no matching exception handler 
  in the current frame). We require that the exception is a valid
  heap address, and that the state before the exception occured
  conforms. 
*} 
lemma uncaught_xcpt_correct:
  assumes wt: "wf_jvm_prog\<^sub>\<Phi> P"
  assumes h:  "h xcp = Some (Obj xcpC xcpFs)"
  shows "\<And>f. P,\<Phi> \<turnstile> (None, h, f#frs)\<surd> \<Longrightarrow> P,\<Phi> \<turnstile> (find_handler P xcp h frs) \<surd>" 
  (is "\<And>f. ?correct (None, h, f#frs) \<Longrightarrow> ?correct (?find frs)")
(*<*)
proof (induct frs) 
  -- "the base
 case is trivial as it should be"
  show "?correct (?find [])" by (simp add: correct_state_def)
next
  -- "we will need both forms @{text wf_jvm_prog} and @{text wf_prog} later"
  from wt obtain mb where wf: "wf_prog mb P" by (simp add: wf_jvm_prog_phi_def)

  -- "the assumption for the cons case:"
  fix f f' frs' assume cr: "?correct (None, h, f#f'#frs')" 

  -- "the induction hypothesis:"
  assume IH: "\<And>f. ?correct (None, h, f#frs') \<Longrightarrow> ?correct (?find frs')" 

  from cr have cr': "?correct (None, h, f'#frs')"
    by (fastsimp simp add: correct_state_def)
    
  obtain stk loc C M pc where [simp]: "f' = (stk,loc,C,M,pc)" by (cases f')

  from cr obtain Ts T mxs mxl\<^isub>0 ins xt where
    meth: "P \<turnstile> C sees M:Ts \<rightarrow> T = (mxs,mxl\<^isub>0,ins,xt) in C"
    by (simp add: correct_state_def, blast)

  hence [simp]: "ex_table_of P C M = xt" by simp
  
  show "?correct (?find (f'#frs'))" 
  proof (cases "match_ex_table P (cname_of h xcp) pc xt")
    case None with cr' IH [of f'] show ?thesis by fastsimp
  next
    fix pc_d
    assume "match_ex_table P (cname_of h xcp) pc xt = Some pc_d"
    then obtain pc' d' where 
      match: "match_ex_table P (cname_of h xcp) pc xt = Some (pc',d')"
      (is "?match (cname_of h xcp) = _")
      by (cases pc_d) auto 

    from wt meth cr' [simplified]
    have wti: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M" 
      by (fastsimp simp add: correct_state_def conf_f_def
                   dest: sees_method_fun
                   elim!: wt_jvm_prog_impl_wt_instr)
    from cr meth
    obtain n M' ST LT where
      ins: "ins!pc = Invoke n M'" (is "_ = ?i") and
      \<Phi>: "\<Phi> C M ! pc = Some (ST, LT)"
      by (fastsimp dest: sees_method_fun simp add: correct_state_def)
    
    from ins match obtain f t D where
      rel: "(f,t,D,pc',d') \<in> set (relevant_entries P (ins!pc) pc xt)" and
      D: "P \<turnstile> cname_of h xcp \<preceq>\<^sup>* D"
      by (fastsimp dest: Invoke_handlers)
    
    from rel have 
      "(pc', Some (Class D # drop (size ST - d') ST, LT)) \<in> set (xcpt_eff (ins!pc) P pc (ST,LT) xt)"
      (is "(_, Some (?ST',_)) \<in> _")
      by (force simp add: xcpt_eff_def image_def)      
    with wti \<Phi> obtain 
      pc: "pc' < size ins" and
      "P \<turnstile> Some (?ST', LT) \<le>' \<Phi> C M ! pc'"
      by (clarsimp simp add: defs1) blast
    then obtain ST' LT' where
      \<Phi>': "\<Phi> C M ! pc' = Some (ST',LT')" and
      less: "P \<turnstile> (?ST', LT) \<le>\<^sub>i (ST',LT')"
      by (auto simp add: sup_state_opt_any_Some)   
    
    from cr' \<Phi> meth have "conf_f P h (ST, LT) ins f'"
      by (unfold correct_state_def) (fastsimp dest: sees_method_fun)
    hence loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and 
          stk: "P,h \<turnstile> stk [:\<le>] ST" by (unfold conf_f_def) auto
    hence [simp]: "size stk = size ST" by (simp add: list_all2_lengthD)

    let ?f = "(Addr xcp # drop (length stk - d') stk, loc, C, M, pc')"
    have "conf_f P h (ST',LT') ins ?f" 
    proof -
      from wf less loc have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" by simp blast
      moreover from D h have "P,h \<turnstile> Addr xcp :\<le> Class D" 
	by(simp add: conf_def prod_case_unfold)
      with less stk
      have "P,h \<turnstile> Addr xcp # drop (length stk - d') stk  [:\<le>] ST'" 
        by (auto intro!: list_all2_dropI)
      ultimately show ?thesis using pc by (simp add: conf_f_def) 
    qed

    with cr' match \<Phi>' meth pc
    show ?thesis by (unfold correct_state_def) (fastsimp dest: sees_method_fun)
  qed
qed
(*>*)

lemma non_npD: "\<lbrakk> v \<noteq> Null; P,h \<turnstile> v :\<le> Class C; C \<noteq> Object \<rbrakk> \<Longrightarrow> \<exists>a C' fs. v = Addr a \<and> h a = Some(Obj C' fs) \<and> P \<turnstile> C' \<preceq>\<^sup>* C"
(*<*)
apply (drule conf_ClassD)
apply auto
apply(case_tac obj)
apply(auto dest: Array_widen)
done
(*>*)


text {*
  The requirement of lemma @{text uncaught_xcpt_correct} (that
  the exception is a valid reference on the heap) is always met
  for welltyped instructions and conformant states:
*}
lemma exec_instr_xcpt_h:
  "\<lbrakk>  (tas, (\<lfloor>xcp\<rfloor>, \<sigma>)) \<in> set (exec_instr (ins!pc) P h stk vars Cl M pc frs);
       P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M;
       P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk>
  \<Longrightarrow> \<exists>xcpC xcpFs. h xcp = Some (Obj xcpC xcpFs)" 
  (is "\<lbrakk> ?xcpt; ?wt; ?correct \<rbrakk> \<Longrightarrow> ?thesis")
proof -
  note [simp] = split_beta
  note [split] = split_if_asm option.split_asm 
  
  assume wt: ?wt ?correct
  hence pre: "preallocated h" by (simp add: correct_state_def hconf_def)

  assume xcpt: ?xcpt with pre show ?thesis 
  proof (cases "ins!pc")
    case Throw with xcpt wt pre show ?thesis 
      apply (clarsimp iff: list_all2_Cons2 simp add: defs1) 
      by(auto dest: non_npD simp: is_refT_def elim: preallocatedE)
  qed (auto elim: preallocatedE)
qed


lemma conf_sys_xcpt:
  "\<lbrakk>preallocated h; C \<in> sys_xcpts\<rbrakk> \<Longrightarrow> P,h \<turnstile> Addr (addr_of_sys_xcpt C) :\<le> Class C"
  by (auto elim: preallocatedE)

lemma match_ex_table_SomeD:
  "match_ex_table P C pc xt = Some (pc',d') \<Longrightarrow> 
  \<exists>(f,t,D,h,d) \<in> set xt. matches_ex_entry P C pc (f,t,D,h,d) \<and> h = pc' \<and> d=d'"
  by (induct xt) (auto split: split_if_asm)


text {*
  Finally we can state that, whenever an exception occurs, the
  next state always conforms:
*}
lemma xcpt_correct:
  fixes \<sigma>' :: jvm_state
  assumes wtp:  "wf_jvm_prog\<^sub>\<Phi> P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes xp:   "(tas, (\<lfloor>xcp\<rfloor>, \<sigma>)) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  assumes s': "(tas', \<sigma>') = (\<lambda>(tas,  (xcpt', h', frs')). (tas, case xcpt' of None \<Rightarrow> (None,h',frs') | Some a \<Rightarrow> find_handler P a h ((stk,loc,C,M,pc)#frs))) (tas, (\<lfloor>xcp\<rfloor>, \<sigma>))"
  assumes correct: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof -
  from wtp obtain wfmb where wf: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)                

  note conf_sys_xcpt [elim!]
  note xp' = meth s' xp

  note wtp
  moreover
  from xp wt correct
  obtain xcpC xcpFs where h: "h xcp = Some(Obj xcpC xcpFs)" by (blast dest: exec_instr_xcpt_h)
  moreover note correct
  ultimately
  have "P,\<Phi> \<turnstile> find_handler P xcp h frs \<surd>" by (rule uncaught_xcpt_correct)
  with xp'
  have "match_ex_table P (cname_of h xcp) pc xt = None \<Longrightarrow> ?thesis" 
    (is "?m (cname_of h xcp) = _ \<Longrightarrow> _" is "?match = _ \<Longrightarrow> _")
    by simp
  moreover
  { fix pc_d assume "?match = Some pc_d"
    then obtain pc' d' where some_handler: "?match = Some (pc',d')" 
      by (cases pc_d) auto
    
    from correct meth
    obtain ST LT where
      h_ok:  "P \<turnstile> h \<surd>" and
      \<Phi>_pc: "\<Phi> C M ! pc = Some (ST, LT)" and
      frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
      frames: "conf_fs P h \<Phi> M (size Ts) T frs"
      by (unfold correct_state_def) (fastsimp dest: sees_method_fun)

    from h_ok have preh: "preallocated h" by (simp add: hconf_def)

    from frame obtain 
      stk: "P,h \<turnstile> stk [:\<le>] ST" and
      loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
      pc:  "pc < size ins" 
      by (unfold conf_f_def) auto
    
    from stk have [simp]: "size stk = size ST" ..

    from wt \<Phi>_pc have
      eff: "\<forall>(pc', s')\<in>set (xcpt_eff (ins!pc) P pc (ST,LT) xt).
             pc' < size ins \<and> P \<turnstile> s' \<le>' \<Phi> C M!pc'"
      by (auto simp add: defs1)     
    
    let ?stk' = "Addr xcp # drop (length stk - d') stk"
    let ?f = "(?stk', loc, C, M, pc')"
    from some_handler xp' 
    have \<sigma>': "\<sigma>' = (None, h, ?f#frs)"
      by (simp add: split_beta)

    from some_handler obtain f t D where
      xt: "(f,t,D,pc',d') \<in> set xt" and
      "matches_ex_entry P (cname_of h xcp) pc (f,t,D,pc',d')"
      by (auto dest: match_ex_table_SomeD)

    hence match: "P \<turnstile> cname_of h xcp \<preceq>\<^sup>* D"  "pc \<in> {f..<t}"
      by (auto simp: matches_ex_entry_def)

    from xp obtain
      "(f,t,D,pc',d') \<in> set (relevant_entries P (ins!pc) pc xt)" and
      conf: "P,h \<turnstile> Addr xcp :\<le> Class D"
    proof (cases "ins!pc")
      case Return
      with xp have False by (auto simp: split_beta split: split_if_asm)
      thus ?thesis ..
    next
      case New with xp
      have [simp]: "xcp = addr_of_sys_xcpt OutOfMemory" by simp
      with New match preh have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
        by (simp add: is_relevant_entry_def)
      with match preh xt
      show ?thesis by (fastsimp simp add: relevant_entries_def intro: that)
    next
      case Getfield with xp
      have [simp]: "xcp = addr_of_sys_xcpt NullPointer" 
        by (simp add: split_beta split: split_if_asm)
      with Getfield match preh have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
        by (simp add: is_relevant_entry_def)
      with match preh xt
      show ?thesis by (fastsimp simp add: relevant_entries_def intro: that)
    next
      case Putfield with xp
      have [simp]: "xcp = addr_of_sys_xcpt NullPointer" 
        by (simp add: split_beta split: split_if_asm)
      with Putfield match preh have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
        by (simp add: is_relevant_entry_def)
      with match preh xt
      show ?thesis by (fastsimp simp add: relevant_entries_def intro: that)
    next
      case Checkcast with xp
      have [simp]: "xcp = addr_of_sys_xcpt ClassCast" 
        by (simp add: split_beta split: split_if_asm)
      with Checkcast match preh have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
        by (simp add: is_relevant_entry_def)
      with match preh xt
      show ?thesis by (fastsimp simp add: relevant_entries_def intro: that)
    next
      case Invoke with xp match 
      have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
        by (simp add: is_relevant_entry_def)
      moreover
      from xp wt correct obtain xcpC xcpFs where xcp: "h xcp = Some(Obj xcpC xcpFs)"
        by (blast dest: exec_instr_xcpt_h)
      ultimately
      show ?thesis using xt match
        by (auto simp add: relevant_entries_def conf_def prod_case_unfold intro: that)
    next
      case Throw with xp match preh 
      have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
        by (simp add: is_relevant_entry_def)
      moreover
      from xp wt correct obtain xcpC xcpFs where xcp: "h xcp = Some(Obj xcpC xcpFs)"
        by (blast dest: exec_instr_xcpt_h)
      ultimately
      show ?thesis using xt match
        by (auto simp add: relevant_entries_def conf_def prod_case_unfold intro: that)
    next
      case ALoad with xp match preh 
      have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
	by (auto simp add: is_relevant_entry_def split_beta split: split_if_asm)
      moreover
      from xp wt correct obtain xcpC xcpFs where xcp: "h xcp = Some(Obj xcpC xcpFs)"
        by (blast dest: exec_instr_xcpt_h)
      ultimately
      show ?thesis using xt match
        by (auto simp add: relevant_entries_def conf_def prod_case_unfold intro: that)
    next
      case AStore with xp match preh 
      have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
	by (auto simp add: is_relevant_entry_def split_beta split: split_if_asm)
      moreover
      from xp wt correct obtain xcpC xcpFs where xcp: "h xcp = Some(Obj xcpC xcpFs)"
        by (blast dest: exec_instr_xcpt_h)
      ultimately
      show ?thesis using xt match
        by (auto simp add: relevant_entries_def conf_def prod_case_unfold intro: that)
    next
      case NewArray with xp match preh 
      have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
	by (auto simp add: is_relevant_entry_def split_beta split: split_if_asm)
      moreover
      from xp wt correct obtain xcpC xcpFs where xcp: "h xcp = Some(Obj xcpC xcpFs)"
        by (blast dest: exec_instr_xcpt_h)
      ultimately
      show ?thesis using xt match
        by (auto simp add: relevant_entries_def conf_def prod_case_unfold intro: that)
    next
      case MEnter with xp match preh 
      have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
	by (auto simp add: is_relevant_entry_def split_beta split: split_if_asm)
      moreover
      from xp wt correct obtain xcpC xcpFs where xcp: "h xcp = Some(Obj xcpC xcpFs)"
        by (blast dest: exec_instr_xcpt_h)
      ultimately
      show ?thesis using xt match
        by (auto simp add: relevant_entries_def conf_def prod_case_unfold intro: that)
    next
      case MExit with xp match preh 
      have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
	by (auto simp add: is_relevant_entry_def split_beta split: split_if_asm)
      moreover
      from xp wt correct obtain xcpC xcpFs where xcp: "h xcp = Some(Obj xcpC xcpFs)"
        by (blast dest: exec_instr_xcpt_h)
      ultimately
      show ?thesis using xt match
        by (auto simp add: relevant_entries_def conf_def prod_case_unfold intro: that)
    qed auto

    with eff obtain ST' LT' where
      \<Phi>_pc': "\<Phi> C M ! pc' = Some (ST', LT')" and
      pc':   "pc' < size ins" and
      less:  "P \<turnstile> (Class D # drop (size ST - d') ST, LT) \<le>\<^sub>i (ST', LT')"
      by (fastsimp simp add: xcpt_eff_def sup_state_opt_any_Some)

    with conf loc stk have "conf_f P h (ST',LT') ins ?f" 
      by (auto simp add: defs1 intro: list_all2_dropI)
    with meth h_ok frames \<Phi>_pc' \<sigma>'
    have ?thesis by (unfold correct_state_def) (fastsimp dest: sees_method_fun)
  }
  ultimately
  show ?thesis by (cases "?match") blast+ 
qed
(*>*)


section {* Single Instructions *}

text {*
  In this section we prove for each single (welltyped) instruction
  that the state after execution of the instruction still conforms.
  Since we have already handled exceptions above, we can now assume that
  no exception occurs in this step.
*}

declare defs1 [simp]



lemma Invoke_correct: 
  fixes \<sigma>' :: jvm_state
  assumes wtprog: "wf_jvm_prog\<^sub>\<Phi> P"
  assumes meth_C: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes ins:    "ins ! pc = Invoke M' n"
  assumes wti:    "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes \<sigma>': "\<sigma>' = (None, \<sigma>)"
  assumes approx: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_xcp: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>" 
(*<*)
proof -
  note split_paired_Ex [simp del]
  
  from wtprog obtain wfmb where wfprog: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)
      
  from ins meth_C approx obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs"
    by (fastsimp dest: sees_method_fun)

  from ins wti \<Phi>_pc
  have n: "n < size ST" by simp
  
  { assume "stk!n = Null"
    with ins no_xcp have False by (simp add: split_beta)
    hence ?thesis ..
  } 
  moreover
  { assume "ST!n = NT"
    moreover 
    from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
    with n have "P,h \<turnstile> stk!n :\<le> ST!n" by (simp add: list_all2_conv_all_nth)
    ultimately 
    have "stk!n = Null" by simp
    with ins no_xcp have False by (simp add: split_beta)
    hence ?thesis ..
  } 
  moreover
  { assume NT: "ST!n \<noteq> NT" and Null: "stk!n \<noteq> Null"

    from frame obtain 
      stk: "P,h \<turnstile> stk [:\<le>] ST" and
      loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" by simp

    from NT ins wti \<Phi>_pc have pc': "pc+1 < size ins" by simp

    from NT ins wti \<Phi>_pc obtain ST' LT'
      where pc': "pc+1 < size ins"
      and \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')"
      and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'"
      by(fastsimp simp add: neq_Nil_conv sup_state_opt_any_Some split: split_if_asm dest: no_sees_wait[OF wfprog])
    with NT ins wti \<Phi>_pc
    have "(\<exists>D D' Ts T m. ST!n = Class D \<and> P \<turnstile> D sees M': Ts\<rightarrow>T = m in D' \<and> P \<turnstile> rev (take n ST) [\<le>] Ts \<and> P \<turnstile> (T # drop (n+1) ST) [\<le>] ST') \<or>
          (\<exists>D. ST!n = Class D \<and> (M' = start \<or> M' = join) \<and> n = 0 \<and> P \<turnstile> D \<preceq>\<^sup>* Thread \<and> P \<turnstile> (Void # drop (n+1) ST) [\<le>] ST') \<or>
          (is_refT (ST ! n) \<and> (M' = wait \<or> M' = notify \<or> M' = notifyAll) \<and> n = 0 \<and> P \<turnstile> (Void # drop (n+1) ST) [\<le>] ST')"
      by(fastsimp split: split_if_asm simp add: split_beta
                  dest: no_sees_wait[OF wfprog] Thread_not_sees_method_start[OF wfprog] no_sees_notify[OF wfprog]
                        no_sees_notifyAll[OF wfprog] Thread_not_sees_method_join[OF wfprog])
    moreover
    { fix D D' Ts T m
      assume  D: "ST!n = Class D"
	and m_D: "P \<turnstile> D sees M': Ts\<rightarrow>T = m in D'"
	and Ts:  "P \<turnstile> rev (take n ST) [\<le>] Ts"
	and ST': "P \<turnstile> (T # drop (n+1) ST) [\<le>] ST'"
      from n stk D have "P,h \<turnstile> stk!n :\<le> Class D"
	by (auto simp add: list_all2_conv_all_nth)

      from m_D wtprog have DObject: "D \<noteq> Object"
	by(auto dest: wf_Object_method_empty simp add: wf_jvm_prog_phi_def)
      from `P,h \<turnstile> stk!n :\<le> Class D` Null DObject 
      obtain a C' fs where
	Addr:   "stk!n = Addr a" and
	obj:    "h a = Some (Obj C' fs)" and
	C'subD: "P \<turnstile> C' \<preceq>\<^sup>* D"
	by(auto dest!: conf_ClassD, case_tac obj, auto dest: Array_widen)

      with wfprog m_D
      obtain Ts' T' m' D'' mxs' mxl' ins' xt' where
	m_C': "P \<turnstile> C' sees M': Ts'\<rightarrow>T' = (mxs',mxl',ins',xt') in D''" and
	T':   "P \<turnstile> T' \<le> T" and
	Ts':  "P \<turnstile> Ts [\<le>] Ts'" 
	by (auto dest: sees_method_mono)
      
      let ?loc' = "Addr a # rev (take n stk) @ replicate mxl' arbitrary"
      let ?f' = "([], ?loc', D'', M', 0)"
      let ?f  = "(stk, loc, C, M, pc)"
      
      from Addr obj m_C' ins \<sigma>' meth_C no_xcp
      have s': "\<sigma>' = (None, h, ?f' # ?f # frs)"
	by(auto split: split_if_asm
                dest: Thread_not_sees_method_start[OF wfprog] Thread_not_sees_method_join[OF wfprog]
                      no_sees_wait[OF wfprog] no_sees_notify[OF wfprog] no_sees_notifyAll[OF wfprog])
      
      from Ts n have [simp]: "size Ts = n" 
	by (auto dest: list_all2_lengthD simp: min_def)
      with Ts' have [simp]: "size Ts' = n" 
	by (auto dest: list_all2_lengthD)

      from m_C' wfprog
      obtain mD'': "P \<turnstile> D'' sees M':Ts'\<rightarrow>T'=(mxs',mxl',ins',xt') in D''"
	by (fast dest: sees_method_idemp)
      moreover 
      with wtprog 
      obtain start: "wt_start P D'' Ts' mxl' (\<Phi> D'' M')" and ins': "ins' \<noteq> []"
	by (auto dest: wt_jvm_prog_impl_wt_start)    
      then obtain LT\<^isub>0 where LT\<^isub>0: "\<Phi> D'' M' ! 0 = Some ([], LT\<^isub>0)"
	by (clarsimp simp add: wt_start_def defs1 sup_state_opt_any_Some)
      moreover
      have "conf_f P h ([], LT\<^isub>0) ins' ?f'"
      proof -
	let ?LT = "OK (Class D'') # (map OK Ts') @ (replicate mxl' Err)"

	from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
	hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" by simp
	also note Ts also note Ts' finally
	have "P,h \<turnstile> rev (take n stk) [:\<le>\<^sub>\<top>] map OK Ts'" by simp 
	also
	have "P,h \<turnstile> replicate mxl' arbitrary [:\<le>\<^sub>\<top>] replicate mxl' Err" 
          by simp
	also from m_C' have "P \<turnstile> C' \<preceq>\<^sup>* D''" by (rule sees_method_decl_above)
	with obj have "P,h \<turnstile> Addr a :\<le> Class D''" by (simp add: conf_def)
	ultimately
	have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] ?LT" by simp
	also from start LT\<^isub>0 have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT\<^isub>0" by (simp add: wt_start_def)
	finally have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] LT\<^isub>0" .
	thus ?thesis using ins' by simp
      qed
      ultimately
      have ?thesis using s' \<Phi>_pc approx meth_C m_D T' ins D 
	by (fastsimp dest: sees_method_fun [of _ C]) }
    moreover
    { fix D
      assume D: "ST!n = Class D"
	and M': "M' = start \<or> M' = join" "n = 0"
	and "P \<turnstile> D \<preceq>\<^sup>* Thread"
	and ST': "P \<turnstile> (Void # drop (n+1) ST) [\<le>] ST'"

      from n stk D have "P,h \<turnstile> stk!n :\<le> Class D"
	by (fastsimp simp add: list_all2_conv_all_nth)
      from `P \<turnstile> D \<preceq>\<^sup>* Thread` have "D \<noteq> Object"
	by-(rule notI, simp)
      with `P,h \<turnstile> stk!n :\<le> Class D` Null `P \<turnstile> D \<preceq>\<^sup>* Thread`
      obtain a C' fs where
	Addr:   "stk!n = Addr a" and
	obj:    "h a = Some (Obj C' fs)" and
	C'subD: "P \<turnstile> C' \<preceq>\<^sup>* D"
	by(auto dest!: conf_ClassD, case_tac obj, auto dest: Array_widen)
      from C'subD `P \<turnstile> D \<preceq>\<^sup>* Thread` have "P \<turnstile> C' \<preceq>\<^sup>* Thread"
	by(rule rtranclp_trans)
      hence "\<sigma>' = (None, h, (Unit # tl stk, loc, C, M, pc + 1) # frs)"
	using Addr obj \<Phi>_pc approx meth_C ins D \<sigma>' no_xcp M'
	by(auto split: split_if_asm simp add: split_beta)
      moreover from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
      moreover from stk ST' M' have "P,h \<turnstile> Unit # tl stk  [:\<le>] ST'"
	by(cases ST, simp, cases stk, auto)
      ultimately have ?thesis using \<Phi>_pc approx meth_C ins D \<Phi>' pc'
	by(fastsimp dest: sees_method_fun) }
    moreover
    { assume "is_refT (ST ! n)"
      and M': "M' = wait \<or> M' = notify \<or> M' = notifyAll"
      and [simp]: "n = 0"
      and ST': "P \<turnstile> (Void # drop (n+1) ST) [\<le>] ST'"
      from n stk NT `is_refT (ST ! n)` Null
      obtain a where "stk!n = Addr a"
	by(auto dest!: conf_ClassD simp add: neq_Nil_conv list_all2_Cons2 conf_def widen_Array widen_Class elim!: refTE)
      with M' have "\<sigma>' = (None, h, (Unit # tl stk, loc, C, M, pc + 1) # frs)"
	using \<Phi>_pc approx meth_C ins \<sigma>' no_xcp
	by(simp split: split_if_asm)
      moreover from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
      moreover from stk ST' have "P,h \<turnstile> Unit # tl stk  [:\<le>] ST'"
	by(cases ST, simp, cases stk, auto)
      ultimately have ?thesis using \<Phi>_pc approx meth_C ins \<Phi>' pc'
	by(fastsimp dest: sees_method_fun) }
    ultimately have ?thesis
      by -(erule disjE | clarify, clarsimp)+ }
  ultimately show ?thesis by blast
qed
(*>*)

declare list_all2_Cons2 [iff]

lemma Return_correct:
  fixes \<sigma>' :: jvm_state
  assumes wt_prog: "wf_jvm_prog\<^sub>\<Phi> P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes ins: "ins ! pc = Return"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "(tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs))"
  assumes correct: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof -
  from wt_prog 
  obtain wfmb where wf: "wf_prog wfmb P" by (simp add: wf_jvm_prog_phi_def)

  from meth ins s'
  have "frs = [] \<Longrightarrow> ?thesis" by (simp add: correct_state_def)
  moreover
  { fix f frs' assume frs': "frs = f#frs'"
    moreover obtain stk' loc' C' M' pc' where 
      f: "f = (stk',loc',C',M',pc')" by (cases f)
    moreover note meth ins s'
    ultimately
    have \<sigma>':
      "\<sigma>' = (None,h,(hd stk#(drop (1+size Ts) stk'),loc',C',M',pc'+1)#frs')"
      (is "\<sigma>' = (None,h,?f'#frs')")
      by simp
    
    from correct meth
    obtain ST LT where
      h_ok:   "P \<turnstile> h \<surd>" and
      \<Phi>_pc: "\<Phi> C M ! pc = Some (ST, LT)" and
      frame:  "conf_f P h (ST, LT) ins (stk,loc,C,M,pc)" and
      frames: "conf_fs P h \<Phi> M (size Ts) T frs"
      by (auto dest: sees_method_fun simp add: correct_state_def)

    from \<Phi>_pc ins wt
    obtain U ST\<^isub>0 where "ST = U # ST\<^isub>0" "P \<turnstile> U \<le> T"
      by (simp add: wt_instr_def app_def) blast    
    with wf frame 
    have hd_stk: "P,h \<turnstile> hd stk :\<le> T" by (auto simp add: conf_f_def)

    from f frs' frames
    obtain ST' LT' Ts'' T'' mxs' mxl\<^isub>0' ins' xt' D Ts' T' m D' where
      \<Phi>': "\<Phi> C' M' ! pc' = Some (ST', LT')" and
      meth_C':  "P \<turnstile> C' sees M':Ts''\<rightarrow>T''=(mxs',mxl\<^isub>0',ins',xt') in C'" and
      ins': "ins' ! pc' = Invoke M (size Ts)" and
      D: "ST' ! (size Ts) = Class D" and
      meth_D: "P \<turnstile> D sees M: Ts'\<rightarrow>T' = m in D'" and
      T': "P \<turnstile> T \<le> T'" and
      frame':   "conf_f P h (ST',LT') ins' f" and
      conf_fs:  "conf_fs P h \<Phi> M' (size Ts'') T'' frs'"
      by clarsimp blast

    from f frame' obtain
      stk': "P,h \<turnstile> stk' [:\<le>] ST'" and
      loc': "P,h \<turnstile> loc' [:\<le>\<^sub>\<top>] LT'" and
      pc':  "pc' < size ins'"
      by (simp add: conf_f_def)
    
    from wt_prog meth_C' pc'  
    have "P,T'',mxs',size ins',xt' \<turnstile> ins'!pc',pc' :: \<Phi> C' M'"
      by (rule wt_jvm_prog_impl_wt_instr)
    with ins' \<Phi>' D meth_D
    obtain aTs ST'' LT'' where
      \<Phi>_suc:   "\<Phi> C' M' ! Suc pc' = Some (ST'', LT'')" and
      less:    "P \<turnstile> (T' # drop (size Ts+1) ST', LT') \<le>\<^sub>i (ST'', LT'')" and
      suc_pc': "Suc pc' < size ins'"
      by(fastsimp simp add: sup_state_opt_any_Some split: split_if_asm
          dest: Thread_not_sees_method_start[OF wf] Thread_not_sees_method_join[OF wf]
                no_sees_wait[OF wf] no_sees_notify[OF wf] no_sees_notifyAll[OF wf])

    from hd_stk T' have hd_stk': "P,h \<turnstile> hd stk :\<le> T'"  ..
        
    have frame'':
      "conf_f P h (ST'',LT'') ins' ?f'" 
    proof -
      from stk'
      have "P,h \<turnstile> drop (1+size Ts) stk' [:\<le>] drop (1+size Ts) ST'" ..
      moreover
      with hd_stk' less
      have "P,h \<turnstile> hd stk # drop (1+size Ts) stk' [:\<le>] ST''" by auto
      moreover
      from wf loc' less have "P,h \<turnstile> loc' [:\<le>\<^sub>\<top>] LT''" by auto
      moreover note suc_pc' 
      ultimately show ?thesis by (simp add: conf_f_def)
    qed

    with \<sigma>' frs' f meth h_ok hd_stk \<Phi>_suc frames meth_C' \<Phi>'  
    have ?thesis by (fastsimp dest: sees_method_fun [of _ C'])
  }
  ultimately
  show ?thesis by (cases frs) blast+
qed

declare sup_state_opt_any_Some [iff]
declare not_Err_eq [iff] 

lemma Load_correct:
"\<lbrakk> wf_prog wt P;
    P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
    ins!pc = Load idx; 
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs)); 
    P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk>
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
  by (fastsimp dest: sees_method_fun [of _ C] elim!: confTs_confT_sup)

lemma Store_correct:
"\<lbrakk> wf_prog wt P;
  P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C;
  ins!pc = Store idx;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M;
  (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs));
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk>
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
  apply clarsimp 
  apply (drule (1) sees_method_fun)
  apply clarsimp
  apply (blast intro!: list_all2_update_cong2)
  done
(*>*)


lemma Push_correct:
"\<lbrakk> wf_prog wt P;
    P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
    ins!pc = Push v;
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs));
    P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk>
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>" 
(*<*)
  apply clarsimp 
  apply (drule (1) sees_method_fun)
  apply clarsimp
  apply (blast dest: typeof_lit_conf)
  done
(*>*)


lemma Cast_conf2:
  "\<lbrakk> wf_prog ok P; P,h \<turnstile> v :\<le> T; is_refT T; cast_ok P C h v; 
     P \<turnstile> C \<le> T'; is_type P C\<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> v :\<le> T'"
(*<*)
  apply (unfold cast_ok_def is_refT_def)
  apply(auto simp add: conf_def intro: widen_trans)
  done
(*>*)


lemma Checkcast_correct:
"\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P;
    P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
    ins!pc = Checkcast D; 
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    \<sigma>' = (None, \<sigma>);
    P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>;
    (tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs) \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
  apply (clarsimp simp add: wf_jvm_prog_phi_def split: split_if_asm)
  apply (drule (1) sees_method_fun)
  apply (blast intro: Cast_conf2)
  done
(*>*)

declare split_paired_All [simp del]

lemmas widens_Cons [iff] = list_all2_Cons1 [of "widen P", standard]

lemma Getfield_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes i:  "ins!pc = Getfield F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "\<sigma>' = (None, \<sigma>)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes xc: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "P \<turnstile> h \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h \<Phi> M (size Ts) T frs"
    by (fastsimp dest: sees_method_fun)
       
  from i \<Phi> wt obtain oT ST'' vT ST' LT' vT' where 
    oT: "P \<turnstile> oT \<le> Class D" and
    ST: "ST = oT # ST''" and
    F:  "P \<turnstile> D sees F:vT in D" and
    pc': "pc+1 < size ins"  and
    \<Phi>': "\<Phi> C M ! (pc+1) = Some (vT'#ST', LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and  
    vT': "P \<turnstile> vT \<le> vT'"
    by fastsimp                       

  from stk ST obtain ref stk' where 
    stk': "stk = ref#stk'" and
    ref:  "P,h \<turnstile> ref :\<le> oT" and
    ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
    by auto

  from F wf have DObject: "D \<noteq> Object"
    by(auto dest: wf_Object_field_empty has_fields_fun simp add: sees_field_def)
  moreover
  from stk' i mC s' xc have "ref \<noteq> Null"
    by (simp add: split_beta split:split_if_asm)
  moreover from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
  ultimately obtain a D' fs where 
    a: "ref = Addr a" and h: "h a = Some (Obj D' fs)" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
    by (blast dest: non_npD)

  from D' F have has_field: "P \<turnstile> D' has F:vT in D"      
    by (blast intro: has_field_mono has_visible_field)
  moreover from "h\<surd>" h have "P,h \<turnstile> (Obj D' fs) \<surd>" by (rule hconfD)
  ultimately obtain v where v: "fs (F, D) = Some v" "P,h \<turnstile> v :\<le> vT"
    by (clarsimp simp add: oconf_def has_field_def)        
       (blast dest: has_fields_fun)

  from a h i mC s' stk' v xc
  have "\<sigma>' = (None, h, (v#stk',loc,C,M,pc+1)#frs)" by simp
  moreover
  from ST'' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" ..
  moreover
  from v vT' have "P,h \<turnstile> v :\<le> vT'" by blast
  moreover
  from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
  moreover
  note "h\<surd>" mC \<Phi>' pc' v fs
  ultimately
  show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastsimp
qed
(*>*)

lemma Putfield_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes i:  "ins!pc = Putfield F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "\<sigma>' = (None, \<sigma>)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes xc: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "P \<turnstile> h \<surd>" and    
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h \<Phi> M (size Ts) T frs"
    by (fastsimp dest: sees_method_fun)
  
  from i \<Phi> wt obtain vT vT' oT ST'' ST' LT' where 
    ST: "ST = vT # oT # ST''" and
    field: "P \<turnstile> D sees F:vT' in D" and
    oT: "P \<turnstile> oT \<le> Class D" and vT: "P \<turnstile> vT \<le> vT'" and
    pc': "pc+1 < size ins" and 
    \<Phi>': "\<Phi> C M!(pc+1) = Some (ST',LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'"
    by clarsimp blast

  from stk ST obtain v ref stk' where 
    stk': "stk = v#ref#stk'" and
    v:    "P,h \<turnstile> v :\<le> vT" and 
    ref:  "P,h \<turnstile> ref :\<le> oT" and
    ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
    by auto

  from field wf have DObject: "D \<noteq> Object"
    by(auto dest: wf_Object_field_empty has_fields_fun simp add: sees_field_def)
  moreover
  from stk' i mC s' xc have "ref \<noteq> Null" by (auto simp add: split_beta)
  moreover from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
  ultimately obtain a D' fs where 
    a: "ref = Addr a" and h: "h a = Some (Obj D' fs)" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
    by (blast dest: non_npD)

  from v vT have vT': "P,h \<turnstile> v :\<le> vT'" ..

  from field D' have has_field: "P \<turnstile> D' has F:vT' in D"
    by (blast intro: has_field_mono has_visible_field)

  let ?h' = "h(a\<mapsto>(Obj D' (fs((F, D)\<mapsto>v))))" and ?f' = "(stk',loc,C,M,pc+1)"
  from h have hext: "h \<unlhd> ?h'" by (rule hext_upd_obj) 

  from a h i mC s' stk' xc
  have "\<sigma>' = (None, ?h', ?f'#frs)" by simp
  moreover
  from "h\<surd>" h have "P,h \<turnstile> (Obj D' fs)\<surd>" by (rule hconfD) 
  with has_field vT' have "P,h \<turnstile> (Obj D' (fs((F, D)\<mapsto>v)))\<surd>" ..
  with "h\<surd>" h have "P \<turnstile> ?h'\<surd>" by (rule hconf_upd_obj)
  moreover
  from ST'' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" ..
  from this hext have "P,?h' \<turnstile> stk' [:\<le>] ST'" by (rule confs_hext)
  moreover
  from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
  from this hext have "P,?h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" by (rule confTs_hext)
  moreover
  from fs hext
  have "conf_fs P ?h' \<Phi> M (size Ts) T frs" by (rule conf_fs_hext)
  moreover
  note mC \<Phi>' pc' 
  ultimately
  show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastsimp
qed
(*>*)
  

lemma New_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes ins:  "ins!pc = New X"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes exec: "\<sigma>' = (None, \<sigma>)"
  assumes conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs"
    by (auto dest: sees_method_fun)

  from \<Phi>_pc ins wt
  obtain ST' LT' where
    is_class_X: "is_class P X" and
    mxs:       "size ST < mxs" and
    suc_pc:     "pc+1 < size ins" and
    \<Phi>_suc:      "\<Phi> C M!(pc+1) = Some (ST', LT')" and
    less:       "P \<turnstile> (Class X # ST, LT) \<le>\<^sub>i (ST', LT')"
    by auto

  from ins no_x obtain oref where new_Addr: "new_Addr h = Some oref" by auto
  hence h: "h oref = None" by (rule new_Addr_SomeD) 
  
  with exec ins meth new_Addr no_x have \<sigma>':
    "\<sigma>' = (None, h(oref \<mapsto> blank P X), (Addr oref#stk,loc,C,M,pc+1)#frs)"
    (is "\<sigma>' = (None, ?h', ?f # frs)")
    by simp    
  moreover
  from wf h heap_ok is_class_X have h': "P \<turnstile> ?h' \<surd>"
    by (auto intro: hconf_new)
  moreover
  from h frame less suc_pc wf
  have "conf_f P ?h' (ST', LT') ins ?f"
    apply (clarsimp simp add: fun_upd_apply conf_def blank_def split_beta)
    apply (auto intro: confs_hext confTs_hext)
    done      
  moreover
  from h have "h \<unlhd> ?h'" by simp
  with frames have "conf_fs P ?h' \<Phi> M (size Ts) T frs" by (rule conf_fs_hext)
  ultimately
  show ?thesis using meth \<Phi>_suc by fastsimp 
qed
(*>*)


lemma Goto_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
  ins ! pc = Goto branch; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs)) ; 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply clarsimp 
apply (drule (1) sees_method_fun)
apply fastsimp
done
(*>*)


lemma IfFalse_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
  ins ! pc = IfFalse branch; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs)); 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply clarsimp
apply (drule (1) sees_method_fun)
apply fastsimp
done
(*>*)

lemma CmpEq_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
  ins ! pc = CmpEq;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs));
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply clarsimp
apply (drule (1) sees_method_fun)
apply fastsimp
done
(*>*)

lemma Pop_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
  ins ! pc = Pop;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs)); 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply clarsimp
apply (drule (1) sees_method_fun)
apply fastsimp
done
(*>*)


lemma IAdd_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
  ins ! pc = IAdd; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs)); 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply (clarsimp simp add: conf_def)
apply (drule (1) sees_method_fun)
apply fastsimp
done
(*>*)


lemma Throw_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C; 
  ins ! pc = Throw; 
  \<sigma>' = (None, \<sigma>);
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>;
  (tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)\<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
  by simp

lemma NewArray_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes ins:  "ins!pc = NewArray X"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes exec: "\<sigma>' = (None, \<sigma>)"
  assumes conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs"
    by (auto dest: sees_method_fun)

  from ins \<Phi>_pc wt obtain ST'' X' ST' LT' where 
    ST: "ST = Integer # ST''" and
    pc': "pc+1 < size ins"  and
    \<Phi>': "\<Phi> C M ! (pc+1) = Some (X'#ST', LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
    XX': "P \<turnstile> X\<lfloor>\<rceil> \<le> X'" and
    suc_pc:     "pc+1 < size ins" and
    is_type_X: "is_type P X"
    by(fastsimp dest: Array_widen)

  from stk ST obtain si stk' where si: "stk = Intg si # stk'"
    by(auto simp add: conf_def)
  with ins no_x have si': "si \<ge> 0"
    by(auto split: split_if_asm)

  from ins no_x obtain oref where new_Addr: "new_Addr h = Some oref" 
    by(auto split: split_if_asm)
  hence h: "h oref = None" by (rule new_Addr_SomeD) 

  with exec ins meth new_Addr si si' no_x have \<sigma>':
    "\<sigma>' = (None, h(oref \<mapsto> Arr X si (\<lambda>i. default_val X)), (Addr oref#tl stk,loc,C,M,pc+1)#frs)"
    (is "\<sigma>' = (None, ?h', ?f # frs)")
    by(auto split: split_if_asm)
  moreover
  from is_type_X have "P,h \<turnstile> Arr X si (\<lambda>i. default_val X) \<surd>"
    by(simp add: oconf_def)
  with wf h heap_ok have h': "P \<turnstile> ?h' \<surd>"
    by -(rule hconf_new)
  moreover
  from h frame ST' ST LT' suc_pc wf XX'
  have "conf_f P ?h' (X' # ST', LT') ins ?f"
    apply (clarsimp simp add: fun_upd_apply conf_def blank_def split_beta)
    by(auto intro: confs_hext confTs_hext)
  moreover
  from h have "h \<unlhd> ?h'" by simp
  with frames have "conf_fs P ?h' \<Phi> M (size Ts) T frs" by (rule conf_fs_hext)
  ultimately
  show ?thesis using meth \<Phi>' by fastsimp 
qed
(*>*)

lemma ALoad_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes ins:  "ins!pc = ALoad"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes exec: "\<sigma>' = (None, \<sigma>)"
  assumes conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 1" by(auto)

  { assume "hd (tl stk) = Null"
    with ins no_x have False
      by(simp add: split_beta)
    hence ?thesis ..
  } 
  moreover
  { assume "hd (tl ST) = NT"
    moreover 
    from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
    with lST have "P,h \<turnstile> hd (tl stk) :\<le> hd (tl ST)"
      by (cases ST, auto, case_tac list, auto)
    ultimately 
    have "hd (tl stk) = Null" by simp
    with ins no_x have False by (simp add: split_beta)
    hence ?thesis ..
  } 
  moreover {
    assume stkNN: "hd (tl stk) \<noteq> Null"
      and STNN: "hd (tl ST) \<noteq> NT"

    with ins \<Phi>_pc wt obtain ST'' X X' ST' LT' where 
      ST: "ST = Integer # X\<lfloor>\<rceil> # ST''" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (X'#ST', LT')" and
      ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      XX': "P \<turnstile> X \<le> X'" and
      suc_pc:     "pc+1 < size ins"
      by(fastsimp)

    from stk ST obtain ref idx stk' where 
      stk': "stk = idx#ref#stk'" and
      idx: "P,h \<turnstile> idx :\<le> Integer" and
      ref:  "P,h \<turnstile> ref :\<le> X\<lfloor>\<rceil>" and
      ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    with ref obtain a Xel si el 
      where a: "ref = Addr a"
      and ha: "h a = \<lfloor>Arr Xel si el\<rfloor>"
      and Xel: "P \<turnstile> Xel \<le> X"
      by(fastsimp simp add: conf_def widen_Array)
    from heap_ok ha have objok: "P,h \<turnstile> Arr Xel si el \<surd>"
      by(auto simp add: hconf_def)

    from idx obtain idxI where idxI: "idx = Intg idxI"
      by(auto simp add: conf_def)
    with ins idxI idx no_x a ha stk' have si': "idxI \<ge> 0" "idxI < si"
      by(auto simp add: split_beta split: split_if_asm)

    with exec ins meth si' stk' a ha no_x idxI idx have \<sigma>':
      "\<sigma>' = (None, h, (el (the_Intg idx) # stk', loc, C, M, pc + 1) # frs)"
      (is "\<sigma>' = (None, ?h', ?f # frs)")
      by(simp)
    moreover
    from ST stk stk' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" by(auto)
    with frame ST' ST LT' suc_pc wf XX' Xel idxI si' objok
    have "conf_f P ?h' (X' # ST', LT') ins ?f"
      by(fastsimp intro: widen_trans simp add: fun_upd_apply conf_def blank_def split_beta oconf_def)
    ultimately have ?thesis using meth \<Phi>' heap_ok \<Phi>_pc frames by fastsimp }
  ultimately show ?thesis by blast
qed


lemma AStore_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes ins:  "ins!pc = AStore"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes exec: "\<sigma>' = (None, \<sigma>)"
  assumes conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 2" by(auto)

  { assume "hd (tl (tl stk)) = Null"
    with ins no_x have False
      by(simp add: split_beta)
    hence ?thesis ..
  } 
  moreover
  { assume "hd (tl (tl ST)) = NT"
    moreover 
    from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
    with lST have "P,h \<turnstile> hd (tl (tl stk)) :\<le> hd (tl (tl ST))"
      by (cases ST, auto, case_tac list, auto, case_tac lista, auto)
    ultimately 
    have "hd (tl (tl stk)) = Null" by simp
    with ins no_x have False by (simp add: split_beta)
    hence ?thesis ..
  } 
  moreover {
    assume stkNN: "hd (tl (tl stk)) \<noteq> Null"
      and STNN: "hd (tl (tl ST)) \<noteq> NT"

    with ins \<Phi>_pc wt obtain ST'' Y X ST' LT' where 
      ST: "ST = Y # Integer # X\<lfloor>\<rceil> # ST''" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
      ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      suc_pc:     "pc+1 < size ins"
      by(fastsimp)

    from stk ST obtain ref e idx stk' where 
      stk': "stk = e#idx#ref#stk'" and
      idx: "P,h \<turnstile> idx :\<le> Integer" and
      ref:  "P,h \<turnstile> ref :\<le> X\<lfloor>\<rceil>" and
      e: "P,h \<turnstile> e :\<le> Y" and
      ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    with ref obtain a Xel si el 
      where a: "ref = Addr a"
      and ha: "h a = \<lfloor>Arr Xel si el\<rfloor>"
      and Xel: "P \<turnstile> Xel \<le> X"
      by(fastsimp simp add: conf_def widen_Array)

    from idx obtain idxI where idxI: "idx = Intg idxI"
      by(auto simp add: conf_def)
    with ins idx no_x a ha stk' have si': "idxI \<ge> 0" "idxI < si"
      by(auto simp add: split_beta split: split_if_asm)

    from ins idx idxI no_x a ha stk' have cast: "cast_ok P Xel h e"
      by(auto simp add: split_beta split: split_if_asm)
    hence eXel: "P,h \<turnstile> e :\<le> Xel"
      by(auto simp add: cast_ok_def conf_def)

    from cast si' exec ins meth stk' a ha no_x idxI idx have \<sigma>':
      "\<sigma>' = (None, h(a \<mapsto> Arr Xel si (el(idxI := e))), (stk', loc, C, M, pc + 1) # frs)"
      (is "\<sigma>' = (None, ?h', ?f # frs)")
      by(auto)
    moreover
    from heap_ok ha si' idx idxI ha eXel have "P,h \<turnstile> Arr Xel si (el(idxI := e)) \<surd>"
      by(auto dest!: hconfD simp add: oconf_def fun_upd_def)
    with heap_ok ha have "P \<turnstile> ?h' \<surd>"
      by(auto intro!: hconf_upd_arr)
    moreover
    from ha have hext: "h \<unlhd> ?h'"
      by(auto intro!: hextI simp add: fun_upd_def)
    from ST stk stk' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" by auto
    with hext have stk'': "P,?h' \<turnstile> stk' [:\<le>] ST'"
      by- (rule confs_hext)
    moreover
    from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
    with hext have "P,?h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" by - (rule confTs_hext)
    moreover
    with frame ST' ST LT' suc_pc wf Xel idxI si' stk''
    have "conf_f P ?h' (ST', LT') ins ?f"
      by(clarsimp)
    with frames hext have "conf_fs P ?h' \<Phi> M (size Ts) T frs" by- (rule conf_fs_hext)
    ultimately have ?thesis using meth \<Phi>' heap_ok \<Phi>_pc suc_pc
      by(fastsimp) }
  ultimately show ?thesis by blast
qed


lemma MEnter_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes ins:  "ins!pc = MEnter"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes exec: "\<sigma>' = (None, \<sigma>)"
  assumes conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 0" by(auto)

  { assume "hd stk = Null"
    with ins no_x have False
      by(simp add: split_beta)
    hence ?thesis ..
  } 
  moreover
  { assume "hd ST = NT"
    moreover 
    from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
    with lST have "P,h \<turnstile> hd stk :\<le> hd ST"
      by (cases ST, auto)
    ultimately 
    have "hd stk = Null" by simp
    with ins no_x have False by (simp add: split_beta)
    hence ?thesis ..
  } 
  moreover {
    assume stkNN: "hd stk \<noteq> Null"
      and STNN: "hd ST \<noteq> NT"

    with ins \<Phi>_pc wt obtain ST'' X ST' LT' where 
      ST: "ST = X # ST''" and
      refT: "is_refT X" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
      ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      suc_pc:     "pc+1 < size ins"
      by(fastsimp)

    from stk ST obtain ref stk' where 
      stk': "stk = ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> X"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    with ref refT obtain a obj
      where a: "ref = Addr a"
      and ha: "h a = obj"
      by(auto elim!: refTE simp add: conf_def widen_Array widen_Class)

    moreover
    from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
    moreover
    from ST stk stk' ST'
    have "P,h \<turnstile> stk' [:\<le>] ST'" by(auto)
    ultimately 
    have ?thesis using meth \<Phi>' heap_ok \<Phi>_pc suc_pc frames loc LT' exec no_x ins stk' ST'
      by(fastsimp) }
  ultimately show ?thesis by blast
qed

lemma MExit_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C"
  assumes ins:  "ins!pc = MExit"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes exec: "\<sigma>' = (None, \<sigma>)"
  assumes conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, None, \<sigma>) \<in> set (exec_instr (ins!pc) P h stk loc C M pc frs)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 0" by(auto)

  { assume "hd stk = Null"
    with ins no_x have False
      by(simp add: split_beta)
    hence ?thesis ..
  } 
  moreover
  { assume "hd ST = NT"
    moreover 
    from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
    with lST have "P,h \<turnstile> hd stk :\<le> hd ST"
      by (cases ST, auto)
    ultimately 
    have "hd stk = Null" by simp
    with ins no_x have False by (simp add: split_beta)
    hence ?thesis ..
  } 
  moreover {
    assume stkNN: "hd stk \<noteq> Null"
      and STNN: "hd ST \<noteq> NT"

    with ins \<Phi>_pc wt obtain ST'' X ST' LT' where 
      ST: "ST = X # ST''" and
      refT: "is_refT X" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
      ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      suc_pc:     "pc+1 < size ins"
      by(fastsimp)

    from stk ST obtain ref stk' where 
      stk': "stk = ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> X"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    with ref refT obtain a obj
      where a: "ref = Addr a"
      and ha: "h a = obj"
      by(auto elim!: refTE simp add: conf_def widen_Array widen_Class)

    moreover
    from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
    moreover
    from ST stk stk' ST'
    have "P,h \<turnstile> stk' [:\<le>] ST'" by(auto)
    ultimately 
    have ?thesis using meth \<Phi>' heap_ok \<Phi>_pc suc_pc frames loc LT' exec no_x ins stk' ST'
      by(fastsimp) }
  ultimately show ?thesis by blast
qed

text {*
  The next theorem collects the results of the sections above,
  i.e.~exception handling and the execution step for each 
  instruction. It states type safety for single step execution:
  in welltyped programs, a conforming state is transformed
  into another conforming state when one instruction is executed.
*}
theorem instr_correct:
"\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P;
  P \<turnstile> C sees M:Ts\<rightarrow>T=(mxs,mxl\<^isub>0,ins,xt) in C;
  (tas, \<sigma>') \<in> set (exec (P, None, h, (stk,loc,C,M,pc)#frs)); 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply (subgoal_tac "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M")
 prefer 2
 apply (erule wt_jvm_prog_impl_wt_instr, assumption)
 apply clarsimp
 apply (drule (1) sees_method_fun)
 apply simp
apply(cases \<sigma>')
apply(clarify)
apply(rename_tac xcpt' h' \<sigma>')
apply(unfold exec.simps Let_def set_map)
apply(clarify)
apply(rename_tac tasl tast tasw xcpt'' h'' \<sigma>'')
apply(case_tac xcpt'')
 prefer 2
 apply(clarify)
 apply(erule xcpt_correct)
     apply(assumption)+
   apply(fastsimp)
  apply(fastsimp)
 apply(fastsimp)
apply (frule wt_jvm_progD, erule exE)
apply (cases "ins ! pc")
apply (rule Load_correct, assumption+)
 prefer 2
 apply(assumption, fastsimp)
apply (rule Store_correct, assumption+)
 prefer 2
 apply(assumption, fastsimp)
apply (rule Push_correct, assumption+)
 prefer 2
 apply(assumption, fastsimp)
apply (rule New_correct, assumption+)
 prefer 2
 apply(assumption, fastsimp, fastsimp)
apply (rule NewArray_correct, assumption+)
 prefer 2
 apply(assumption, simp split: if_splits, fastsimp)
apply (rule ALoad_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
apply (rule AStore_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
apply (rule Getfield_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
apply (rule Putfield_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
apply (rule Checkcast_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
apply (rule Invoke_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
apply (rule Return_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm)
 apply(clarsimp)
 apply(rule conjI)
  apply(fastsimp)
 apply(clarsimp simp add: split_beta)
apply (rule Pop_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(fastsimp)
apply (rule IAdd_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(fastsimp)
apply (rule Goto_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(fastsimp)
apply (rule CmpEq_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(fastsimp)
apply (rule IfFalse_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(fastsimp)
apply (rule Throw_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
apply (rule MEnter_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
apply (rule MExit_correct, assumption+)
 prefer 2
 apply(assumption)
 apply(simp (no_asm_use) only: option.split_asm, blast)
 apply(simp (no_asm_use) only: option.split_asm, fastsimp)
done
(*>*)

section {* Main *}

lemma correct_state_impl_Some_method:
  "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc)#frs)\<surd> 
  \<Longrightarrow> \<exists>m Ts T. P \<turnstile> C sees M:Ts\<rightarrow>T = m in C"
  by fastsimp

lemma BV_correct_1 [rule_format]:
"\<And>\<sigma>. \<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; P,\<Phi> \<turnstile> \<sigma>\<surd>\<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -tas-jvm\<rightarrow> \<sigma>' \<longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply (simp only: split_tupled_all exec_1_iff)
apply (rename_tac xp h frs)
apply (case_tac xp)
 apply (case_tac frs)
  apply simp
 apply (simp only: split_tupled_all)
 apply hypsubst
 apply (frule correct_state_impl_Some_method)
 apply clarify
 apply (rule instr_correct)
 apply assumption+
apply(simp)
done
(*>*)

lemma ex_set_conv: "(\<exists>x. x \<in> set xs) \<longleftrightarrow> xs \<noteq> []"
apply(auto)
apply(auto simp add: neq_Nil_conv)
done


theorem progress:
  "\<lbrakk> xp=None; frs\<noteq>[] \<rbrakk> \<Longrightarrow> \<exists>ta \<sigma>'. P \<turnstile> (xp,h,frs) -ta-jvm\<rightarrow> \<sigma>'"
by(clarsimp simp add: exec_1_iff neq_Nil_conv split_beta ex_set_conv exec_instr_not_empty image_iff Bex_def simp del: split_paired_Ex)

theorem BV_correct [rule_format]:
"\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>' \<rbrakk> \<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>\<surd> \<longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply (simp only: exec_star_def)
apply(erule stepify_pred.induct)
 apply(simp)
apply(clarify)
apply(erule (2) BV_correct_1)
done
(*>*)

lemma hconf_start:   
  assumes wf: "wf_prog wf_mb P"
  shows "P \<turnstile> (start_heap P) \<surd>"
(*<*)
  apply (unfold hconf_def)
  apply (simp add: preallocated_start)
  apply (clarify)
  apply (drule sym)
  apply (unfold start_heap_def)
  apply (insert wf)
  apply (auto simp add: fun_upd_apply is_class_xcpt split: split_if_asm)
  done
(*>*)
    
lemma BV_correct_initial: 
  shows "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; P \<turnstile> C sees M:[]\<rightarrow>T = m in C \<rbrakk>
  \<Longrightarrow> P,\<Phi> \<turnstile> start_state P C M \<surd>"
(*<*)
  apply (cases m)                            
  apply (unfold  start_state_def)
  apply (unfold correct_state_def)
  apply (simp del: defs1)
  apply (rule conjI)
   apply (simp add: wf_jvm_prog_phi_def hconf_start) 
  apply (drule wt_jvm_prog_impl_wt_start, assumption+)
  apply (unfold conf_f_def wt_start_def)
  apply fastsimp
  done
(*>*)

theorem typesafe:
  assumes welltyped:   "wf_jvm_prog\<^sub>\<Phi> P"
  assumes main_method: "P \<turnstile> C sees M:[]\<rightarrow>T = m in C"
  shows "P \<turnstile> start_state P C M -tas-jvm\<rightarrow>* \<sigma>  \<Longrightarrow>  P,\<Phi> \<turnstile> \<sigma> \<surd>"
(*<*)
proof -
  from welltyped main_method
  have "P,\<Phi> \<turnstile> start_state P C M \<surd>" by (rule BV_correct_initial)
  moreover
  assume "P \<turnstile> start_state P C M -tas-jvm\<rightarrow>* \<sigma>"
  ultimately  
  show "P,\<Phi> \<turnstile> \<sigma> \<surd>" using welltyped by - (rule BV_correct)
qed
(*>*)
  
end
