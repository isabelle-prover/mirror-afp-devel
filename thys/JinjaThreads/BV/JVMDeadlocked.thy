(*  Title:      JinjaThreads/BV/JVMDeadlocked.thy
    Author:     Andreas Lochbihler
*)

header{* Preservation of deadlock for the JVMs *}

theory JVMDeadlocked imports BVProgressThreaded begin

lemma map_typeof_hext_mono: (* Move to Objects *)
  "\<lbrakk> map typeof\<^bsub>h\<^esub> vs = map Some Ts; hext h h' \<rbrakk> \<Longrightarrow>  map typeof\<^bsub>h'\<^esub> vs = map Some Ts"
apply(induct vs arbitrary: Ts)
apply(auto simp add: Cons_eq_map_conv intro: hext_typeof_mono)
done

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
    and exec: "(ta, xcp', m', frs') \<in> set (exec P (xcp, h, frs))" 
    and "(xcp, h, frs) = (xcp, h, f # Frs)"
    by(blast elim: jvmd_NormalE)
  hence [simp]: "frs = f # Frs" by auto
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by(cases f, blast)
  from join exec have [simp]: "xcp = None" by(cases xcp, auto)
  from cs obtain Ts T mxs mxl0 ins xt ST LT 
    where "P \<turnstile> h \<surd>"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastsimp simp add: correct_state_def)
  from exec join have [simp]: "xcp = None" by simp
  from sees exec join show ?thesis
  proof(cases "ins ! pc")
    case (Invoke M' n)
    with check exec sees join obtain a ao Ts U Ta 
      where a: "stk ! n = Addr a"
      and n: "n < length stk"
      and ao: "h a = \<lfloor>ao\<rfloor>"
      and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
      and iec: "is_external_call P Ta M' n"
      and wtext: "P \<turnstile> Ta\<bullet>M'(Ts) :: U"
      and Ts: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Ts"
      by(auto simp add: check_def is_Ref_def has_method_def min_def split: split_if_asm heapobj.split_asm elim!: is_ArrE dest: external_call_not_sees_method[OF wfp])
    from exec iec Ta n a sees Invoke join obtain ta' va m''
      where exec': "(ta', va, m'') \<in> set (red_external_list P a M' (rev (take n stk)) h)"
      and ta: "ta = extTA2JVM P ta'"
      and va: "(xcp', m', frs') = extRet2JVM n m'' stk loc C M pc Frs va"
      by(auto simp add: min_def)
    from va have [simp]: "m'' = m'" by(cases va) simp_all
    from exec' have red: "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
      unfolding red_external_list_conv by simp
    from join ta have "Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>" by simp
    from red_external_Join_hext[OF red this hext] ao
    have "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h'\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by simp
    moreover from ao hext obtain ao' where "h' a = \<lfloor>ao'\<rfloor>" by(auto dest: hext_objarrD)
    moreover from hext Ta have "typeof\<^bsub>h'\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>" by(rule hext_typeof_mono)
    ultimately have "(ta, xcp', h', frs') \<in> set (exec P (xcp, h', frs))" using ta a n iec Invoke sees va
      by(cases va)(force simp add: min_def red_external_list_conv)+
    moreover from Ts hext have "map typeof\<^bsub>h'\<^esub> (rev (take n stk)) = map Some Ts"
      by(rule map_typeof_hext_mono)
    with `typeof\<^bsub>h'\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>` `h' a = \<lfloor>ao'\<rfloor>` iec Invoke a n wtext
    have "check_instr (ins ! pc) P h' stk loc C M pc Frs" by(auto simp add: is_Ref_def)
    with check sees have "check P (xcp, h', frs)" by(simp add: check_def)
    ultimately show "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
      by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
  qed(auto simp add: split_beta split: split_if_asm)
qed

lemma must_sync_preserved_d:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and ml: "P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d LT \<wrong>" 
  and LTnempty: "LT \<noteq> {}"
  and hext: "hext h h'"
  and cs: "P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>"
  shows "P \<turnstile> \<langle>(xcp, h', frs)\<rangle>\<^isub>d \<wrong>"
proof(rule multithreaded.must_syncI[OF execd_mthr])
  from ml obtain ta xcp' frs' m'
    where red: "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and LT: "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
    by(auto elim: multithreaded.can_syncE[OF execd_mthr])
  with LTnempty have lj: "(\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
    by(auto simp add: collect_locks_def)
  from red obtain f Frs
    where check: "check P (xcp, h, frs)"
    and exec: "(ta, xcp', m', frs') \<in> set (exec P (xcp, h, frs))"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)
  from lj exec have [simp]: "xcp = None" by(cases xcp, auto)

  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "P \<turnstile> h \<surd>" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs"
    by (fastsimp simp add: correct_state_def dest: sees_method_fun)

  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)

  from lj have "\<exists>ta xcp' h'' frs'. P \<turnstile> Normal (None, h', (stk, loc, C, M, pc) # Frs) -ta-jvmd\<rightarrow> Normal (xcp', h'', frs')"
  proof(rule disjE)
    assume "\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)"
    then obtain l where l: "Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)" by blast
    with meth exec show ?thesis
    proof(cases "ins ! pc")
      case (Invoke M' n)
      with check exec meth l obtain a ao Ts U Ta 
	where a: "stk ! n = Addr a"
	and n: "n < length stk"
	and ao: "h a = \<lfloor>ao\<rfloor>"
	and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
	and iec: "is_external_call P Ta M' n"
	and wtext: "P \<turnstile> Ta\<bullet>M'(Ts) :: U"
	and Ts: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Ts"
	by(auto simp add: check_def is_Ref_def has_method_def min_def split: split_if_asm heapobj.split_asm elim!: is_ArrE dest: external_call_not_sees_method[OF wfp])
      from exec iec Ta n a meth Invoke l obtain ta' va m''
	where exec': "(ta', va, m'') \<in> set (red_external_list P a M' (rev (take n stk)) h)"
	and ta: "ta = extTA2JVM P ta'"
	and va: "(xcp', m', frs') = extRet2JVM n m'' stk loc C M pc Frs va"
	by(auto simp add: min_def)
      from va have [simp]: "m'' = m'" by(cases va) simp_all
      from exec' have red: "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
	unfolding red_external_list_conv by simp
      from l ta have "Lock \<in> set (\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)" by simp
      from red_external_Lock_hext[OF red this hext] ao
      have "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h'\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by simp
      moreover from ao hext obtain ao' where "h' a = \<lfloor>ao'\<rfloor>" by(auto dest: hext_objarrD)
      moreover from hext Ta have "typeof\<^bsub>h'\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>" by(rule hext_typeof_mono)
      ultimately have "(ta, xcp', h', frs') \<in> set (exec P (xcp, h', frs))" using ta a n iec Invoke meth va
	by(cases va)(force simp add: min_def red_external_list_conv)+
      moreover from Ts hext have "map typeof\<^bsub>h'\<^esub> (rev (take n stk)) = map Some Ts"
	by(rule map_typeof_hext_mono)
      with `typeof\<^bsub>h'\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>` `h' a = \<lfloor>ao'\<rfloor>` iec Invoke a n wtext
      have "check_instr (ins ! pc) P h' stk loc C M pc Frs" by(auto simp add: is_Ref_def)
      with check meth have "check P (xcp, h', frs)" by(simp add: check_def)
      ultimately have "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
	by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
      thus ?thesis by auto
    next
      case MEnter
      with meth l exec have "hd stk \<noteq> Null" by(auto)
      with check meth MEnter obtain a where [simp]: "hd stk = Addr a"
	by(auto elim: is_AddrE simp add: check_def is_Ref_def)
      from meth exec have "(ta, xcp', h', frs') \<in> set (exec P (xcp, h', frs))" by(simp add: MEnter)
      moreover from meth check MEnter have "check P (xcp, h', frs)" by(simp add: check_def)
      ultimately have "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
	by -(rule exec_1_d_NormalI, auto simp add: exec_d_def)
      thus ?thesis by auto
    qed(auto split: split_if_asm simp add: finfun_upd_apply)
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
  and hext: "hext h h'"
  shows "\<exists>L'\<subseteq>L. P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d L' \<wrong>"
proof -
  from cl' obtain ta xcp' frs' m'
    where red: "P \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and L: "L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
    by -(erule  multithreaded.can_syncE[OF execd_mthr], auto)
  then obtain f Frs
    where check: "check P (xcp, h', frs)"
    and exec: "(ta, xcp', m', frs') \<in> set (exec P (xcp, h', frs))"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE simp add: finfun_upd_apply)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)
  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "P \<turnstile> h \<surd>" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs"
    by (fastsimp simp add: correct_state_def dest: sees_method_fun)
  have "exec P (xcp, h, f # frs) \<noteq> []" by(rule exec_not_empty)
  with no_type_error[OF wf cs] have check': "check P (xcp, h, frs)"
    by(auto simp add: exec_d_def split: split_if_asm)
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
  show ?thesis
  proof(cases xcp)
    case (Some a)[simp]
    with exec have [simp]: "m' = h'" by(auto)
    from `P,\<Phi> \<turnstile> (xcp, h, frs) \<surd>` obtain D fs where "h a = \<lfloor>Obj D fs\<rfloor>" by(auto simp add: correct_state_def)
    with hext have "cname_of h a = cname_of h' a" by(auto dest: hext_objD)
    with exec have "(ta, xcp', h, frs') \<in> set (exec P (xcp, h, frs))" by auto
    moreover from check have "check P (xcp, h, frs)" by(simp add: check_def)
    ultimately have "P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h, frs')"
      by -(rule exec_1_d_NormalI, simp only: exec_d_def if_True)
    with L have "multithreaded.can_sync (mexecd P) (xcp, frs) h L"
      by(auto intro: multithreaded.can_syncI[OF execd_mthr])
    thus ?thesis by auto
  next
    case None[simp]
    from exec meth have "\<exists>ta' \<sigma>'. (ta', \<sigma>') \<in> set (exec P (xcp, h, frs)) \<and> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>} \<subseteq> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
    proof(cases "ins ! pc")
      case (Invoke M' n)
      show ?thesis
      proof(cases "stk ! n = Null")
	case True with Invoke exec meth show ?thesis by simp
      next
	case False
	with check meth obtain a where a: "stk ! n = Addr a" and n: "n < length stk"
	  by(auto simp add: check_def is_Ref_def Invoke)
	from frame have stk: "P,h \<turnstile> stk [:\<le>] ST" by(auto simp add: conf_f_def)
	hence "P,h \<turnstile> stk ! n :\<le> ST ! n" using n by(rule list_all2_nthD)
	with a obtain ao Ta where ao: "h a = \<lfloor>ao\<rfloor>" and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
	  by(auto split: heapobj.splits simp add: conf_def)
	from hext Ta have Ta': "typeof\<^bsub>h'\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>" by(rule hext_typeof_mono)
	show ?thesis
	proof(cases "is_external_call P Ta M' n")
	  case False
	  with exec meth a Ta Ta' Invoke n ao show ?thesis by(simp add: min_def split_beta)
	next
	  case True
	  with exec meth a Ta Ta' Invoke n ao
	  obtain ta' va h'' where ta': "ta = extTA2JVM P ta'"
	    and va: "(xcp', m', frs') = extRet2JVM n h'' stk loc C M pc Frs va"
	    and exec': "(ta', va, h'') \<in> set (red_external_list P a M' (rev (take n stk)) h')"
	    by(fastsimp simp add: min_def)
	  from va have [simp]: "h'' = m'" by(cases va) simp_all
	  from exec' have red: "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h'\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
	    by(simp add: red_external_list_conv)
	  from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" by(rule list_all2_takeI)
	  then obtain Ts where "map typeof\<^bsub>h\<^esub> (take n stk) = map Some Ts"
	    by(auto simp add: confs_conv_map)
	  hence "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some (rev Ts)" by(simp only: rev_map[symmetric])
	  from red_external_wt_hconf_hext[OF red Ta this hext]
	  obtain ta'' va' h''' where "P \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h\<rangle> -ta''\<rightarrow>ext \<langle>va',h'''\<rangle>"
	    and ta'': "\<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta''\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta''\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>" by auto
	  with True a Ta Invoke meth Ta' n
	  have "(extTA2JVM P ta'', extRet2JVM n h''' stk loc C M pc Frs va') \<in> set (exec P (xcp, h, frs))"
	    by(force simp add: min_def red_external_list_conv)
	  with ta'' ta' show ?thesis by auto
	qed
      qed
    qed(auto split: split_if_asm)
    with check' have "\<exists>ta' \<sigma>'. P \<turnstile> Normal (xcp, h, frs) -ta'-jvmd\<rightarrow> Normal \<sigma>' \<and> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>} \<subseteq> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
      apply clarify
      apply(rule exI conjI)+
      apply(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
      done
    with L show ?thesis
      apply -
      apply(erule exE conjE|rule exI conjI)+
      prefer 2
      apply(rule_tac x'="(fst \<sigma>', snd (snd \<sigma>'))" and m'="fst (snd \<sigma>')" in multithreaded.can_syncI[OF execd_mthr])
      apply auto
      done
  qed
qed


lemma execd_preserve_deadlocked:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and lto: "lock_thread_ok (locks S) (thr S)"
  and cs: "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "preserve_deadlocked JVM_final (mexecd P) S"
proof(unfold_locales)
  from `lock_thread_ok (locks S) (thr S)`
  show "lock_thread_ok (locks S) (thr S)" .
next
  fix tta s t' ta' s' t x ln LT
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "multithreaded.can_sync (mexecd P) x (shr s) LT"
    and LTnempty: "LT \<noteq> {}"
  moreover obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have ml: "P \<turnstile> \<langle>(xcp, shr s, frs)\<rangle>\<^isub>d LT \<wrong>" by auto
  moreover from cs Red have cs': "correct_state_ts P \<Phi> (thr s) (shr s)"
    by-(rule preserves_correct_state_d[OF wf])
  with tst have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>"
    by(auto dest: ts_okD)
  moreover from red have "hext (shr s) (shr s')"
    by(rule execd_hext)
  ultimately have "P \<turnstile> \<langle>(xcp, shr s', frs)\<rangle>\<^isub>d \<wrong>" using LTnempty
    by-(rule must_sync_preserved_d[OF wf])
  thus "multithreaded.must_sync (mexecd P) x (shr s')" by simp
next
  fix tta s t' ta' s' t x ln L
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "multithreaded.can_sync (mexecd P) x (shr s') L"
  moreover obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have ml: "P \<turnstile> \<langle>(xcp, shr s', frs)\<rangle>\<^isub>d L \<wrong>" by auto
  moreover from cs Red have cs': "correct_state_ts P \<Phi> (thr s) (shr s)"
    by-(rule preserves_correct_state_d[OF wf])
  with tst have "P,\<Phi> \<turnstile> (xcp, shr s, frs) \<surd>"
    by(auto dest: ts_okD)
  moreover from red have "hext (shr s) (shr s')"
    by(rule execd_hext)
  ultimately have "\<exists>L' \<subseteq> L. P \<turnstile> \<langle>(xcp, shr s, frs)\<rangle>\<^isub>d L' \<wrong>"
    by-(rule can_sync_devreserp_d[OF wf])
  thus "\<exists>L' \<subseteq> L. multithreaded.can_sync (mexecd P) x (shr s) L'" by simp
qed


text {* and now everything again for the aggresive VM *}

lemma must_lock_d_eq_must_lock:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,\<Phi> \<turnstile> (xcp, h, frs) \<surd> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d \<wrong> = P \<turnstile> \<langle>(xcp, h, frs)\<rangle> \<wrong>"
apply(simp)
apply(rule iffI)
 apply(rule multithreaded.must_syncI[OF exec_mthr])
 apply(erule multithreaded.must_syncE[OF execd_mthr])
 apply(simp only: mexec_eq_mexecd)
 apply(blast)
apply(rule multithreaded.must_syncI[OF execd_mthr])
apply(erule multithreaded.must_syncE[OF exec_mthr])
apply(simp only: mexec_eq_mexecd[symmetric])
apply(blast)
done

lemma can_lock_d_eq_can_lock:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,\<Phi> \<turnstile> (xcp, h, frs) \<surd> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(xcp, h, frs)\<rangle>\<^isub>d L \<wrong> = P \<turnstile> \<langle>(xcp, h, frs)\<rangle> L \<wrong>"
apply(simp)
apply(rule iffI)
 apply(erule multithreaded.can_syncE[OF execd_mthr])
 apply(rule multithreaded.can_syncI[OF exec_mthr])
   apply(simp only: mexec_eq_mexecd)
  apply(assumption)+
apply(erule multithreaded.can_syncE[OF exec_mthr])
apply(rule multithreaded.can_syncI[OF execd_mthr])
 by(simp only: mexec_eq_mexecd)

lemma exec_preserve_deadlocked:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and lto: "lock_thread_ok (locks S) (thr S)"
  and cs: "correct_state_ts P \<Phi> (thr S) (shr S)"
  shows "preserve_deadlocked JVM_final (mexec P) S"
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
    proof(induct rule: execd_mthr.redT_elims[consumes 1, case_names normal acquire])
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
    { fix L
      assume "multithreaded.can_sync (mexec P) x (shr s) L"
	and L: "L \<noteq> {}"
      hence ml: "P \<turnstile> \<langle>(xcp, shr s, frs)\<rangle> L \<wrong>" by simp
      with cst have "P \<turnstile> \<langle>(xcp, shr s, frs)\<rangle>\<^isub>d L \<wrong>"
	by(auto dest: can_lock_d_eq_can_lock[OF wf])
      hence "multithreaded.must_sync (mexecd P) x (shr s')"
	by-(rule preserve_lock_behav.can_lock_preserved[OF preserve_deadlocked.axioms(2)[OF execd_preserve_deadlocked[OF wf lto cs]] Redd redd tst _ L], simp)
      with cst' have "multithreaded.must_sync (mexec P) x (shr s')"
	by(auto dest: must_lock_d_eq_must_lock[OF wf]) }
    note ml = this
    { fix L
      assume "multithreaded.can_sync (mexec P) x (shr s') L"
      hence cl: "P \<turnstile> \<langle>(xcp, shr s', frs)\<rangle> L \<wrong>" by simp
      with cst' have "P \<turnstile> \<langle>(xcp, shr s', frs)\<rangle>\<^isub>d L \<wrong>"
	by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with Redd redd tst
      have "\<exists>L' \<subseteq> L. multithreaded.can_sync (mexecd P) x (shr s) L'"
	by -(rule preserve_lock_behav.can_lock_devreserp[OF preserve_deadlocked.axioms(2)[OF execd_preserve_deadlocked[OF wf lto cs]]], auto)
      then obtain L' where "multithreaded.can_sync (mexecd P) x (shr s) L'" 
	and L': "L'\<subseteq> L" by blast
      with cst have "multithreaded.can_sync (mexec P) x (shr s) L'"
	by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with L' have "\<exists>L' \<subseteq> L. multithreaded.can_sync (mexec P) x (shr s) L'"
	by(blast) }
    note this ml }
  thus ?thesis using lto by(unfold_locales)
qed


end
