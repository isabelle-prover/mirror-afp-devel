(*  Title:      JinjaThreads/BV/JVMDeadlocked.thy
    Author:     Andreas Lochbihler
*)

header{* \isaheader{Preservation of deadlock for the JVMs} *}

theory JVMDeadlocked imports BVProgressThreaded begin

context JVM_heap_conf_base' begin

lemma join_hext:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
  and red: "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
  and join: "Join t' \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
  and hext: "hext h h'"
  shows "P,t \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
proof -
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(blast dest: wt_jvm_progD)
  from red obtain f Frs
    where check: "check P (xcp, h, frs)" 
    and exec: "(ta, xcp', m', frs') \<in> exec P t (xcp, h, frs)"
    and "(xcp, h, frs) = (xcp, h, f # Frs)"
    by(blast elim: jvmd_NormalE)
  hence [simp]: "frs = f # Frs" by auto
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by(cases f, blast)
  from join exec have [simp]: "xcp = None" by(cases xcp, auto)
  from cs obtain Ts T mxs mxl0 ins xt ST LT 
    where "hconf h"
    and tconf: "P,h \<turnstile> t \<surd>t"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl0, ins, xt) in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    and preh: "preallocated h"
    by(fastsimp simp add: correct_state_def)
  from exec join have [simp]: "xcp = None" by simp
  from sees exec join show ?thesis
  proof(cases "ins ! pc")
    case (Invoke M' n)
    with check exec sees join obtain a Ts U Us Ta 
      where a: "stk ! n = Addr a"
      and n: "n < length stk"
      and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
      and iec: "is_external_call P Ta M'"
      and wtext: "P \<turnstile> Ta\<bullet>M'(Us) :: U"
      and sub: "P \<turnstile> Ts [\<le>] Us"
      and Ts: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Ts"
      by(auto simp add: check_def is_Ref_def has_method_def external_WT'_iff split: split_if_asm dest: external_call_not_sees_method)
    from exec iec Ta n a sees Invoke join obtain ta' va m''
      where exec': "(ta', va, m'') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
      and ta: "ta = extTA2JVM P ta'"
      and va: "(xcp', m', frs') = extRet2JVM n m'' stk loc C M pc Frs va"
      by(auto)
    from va have [simp]: "m'' = m'" by(cases va) simp_all
    from Ta Ts wtext sub have wtext': "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : U" by(rule external_WT'.intros)
    with wfp exec' tconf have red: "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
      by(simp add: WT_red_external_list_conv)
    from join ta have "Join t' \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>" by simp
    from red_external_Join_hext[OF red this hext]
    have "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h'\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>" .
    moreover from hext Ta have "typeof_addr h' a = \<lfloor>Ta\<rfloor>" by(rule typeof_addr_hext_mono)
    ultimately have "(ta, xcp', h', frs') \<in> exec P t (xcp, h', frs)" using ta a n iec Invoke sees va
      by(cases ta', cases va)(force intro: red_external_imp_red_external_aggr)+
    moreover from Ts hext have "map typeof\<^bsub>h'\<^esub> (rev (take n stk)) = map Some Ts"
      by(rule map_typeof_hext_mono)
    with `typeof_addr h' a = \<lfloor>Ta\<rfloor>` iec Invoke a n wtext sub
    have "check_instr (ins ! pc) P h' stk loc C M pc Frs"
      by(auto simp add: is_Ref_def intro!: external_WT'.intros)
    with check sees have "check P (xcp, h', frs)" by(simp add: check_def)
    ultimately show "P,t \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
      by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
  qed(auto simp add: split_beta ta_upd_simps split: split_if_asm)
qed

end

context JVM_progress begin

lemma must_sync_preserved_d:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and ml: "execd_mthr.can_sync P t (xcp, frs) h LT" 
  and LTnempty: "LT \<noteq> {}"
  and hext: "hext h h'"
  and hconf': "hconf h'"
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
  shows "execd_mthr.must_sync P t (xcp, frs) h'"
proof(rule execd_mthr.must_syncI)
  from ml obtain ta xcp' frs' m'
    where red: "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and LT: "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
    by(auto elim: execd_mthr.can_syncE)
  with LTnempty have lj: "(\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)) \<or> (\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>)"
    by(auto simp add: collect_locks_def)
  from red obtain f Frs
    where check: "check P (xcp, h, frs)"
    and exec: "(ta, xcp', m', frs') \<in> exec P t (xcp, h, frs)"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)
  from lj exec have [simp]: "xcp = None" by(cases xcp, auto)

  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "hconf h" and
    tconf:  "P,h \<turnstile> t \<surd>t" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs"
    by (fastsimp simp add: correct_state_def dest: sees_method_fun)

  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
  from tconf hext have tconf': "P,h' \<turnstile> t \<surd>t" by(rule tconf_hext_mono)

  from lj have "\<exists>ta \<sigma>'. P,t \<turnstile> Normal (None, h', (stk, loc, C, M, pc) # Frs) -ta-jvmd\<rightarrow> Normal \<sigma>'"
  proof(rule disjE)
    assume "\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)"
    then obtain l where l: "Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)" by blast
    with meth exec show ?thesis
    proof(cases "ins ! pc")
      case (Invoke M' n)
      with check exec meth l obtain a ao Ts U Us Ta 
	where a: "stk ! n = Addr a"
	and n: "n < length stk"
	and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
	and iec: "is_external_call P Ta M'"
	and wtext: "P \<turnstile> Ta\<bullet>M'(Us) :: U"
	and Ts: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Ts"
        and sub: "P \<turnstile> Ts [\<le>] Us"
	by(auto simp add: check_def is_Ref_def has_method_def external_WT'_iff split: split_if_asm dest: external_call_not_sees_method)
      from exec iec Ta n a meth Invoke l obtain ta' va m''
	where exec': "(ta', va, m'') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
	and ta: "ta = extTA2JVM P ta'"
	and va: "(xcp', m', frs') = extRet2JVM n m'' stk loc C M pc Frs va"
	by(auto simp add: min_def)
      from va have [simp]: "m'' = m'" by(cases va) simp_all
      from Ta Ts wtext sub have wtext': "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : U" by(rule external_WT'.intros)
      with wfp exec' tconf have red: "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
	by(simp add: WT_red_external_list_conv)

      from l ta have "Lock \<in> set (\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)" by simp
      from red_external_Lock_hext[OF wfp red this hext hconf']
      obtain va' TA' h''' where "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h'\<rangle> -TA'\<rightarrow>ext \<langle>va',h'''\<rangle>"
        and TA: "collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>TA'\<rbrace>\<^bsub>l\<^esub>" "{t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>TA'\<rbrace>\<^bsub>c\<^esub>}"
        by auto
      moreover from hext Ta have "typeof_addr h' a = \<lfloor>Ta\<rfloor>" by(rule typeof_addr_hext_mono)
      ultimately have "(extTA2JVM P TA', extRet2JVM n h''' stk loc C M pc Frs va') \<in> exec P t (xcp, h', frs)"
        using ta a n iec Invoke meth va by(cases TA')(auto dest!: red_external_imp_red_external_aggr intro: rev_image_eqI)
        
      moreover from Ts hext have "map typeof\<^bsub>h'\<^esub> (rev (take n stk)) = map Some Ts"
	by(rule map_typeof_hext_mono)
      with `typeof_addr h' a = \<lfloor>Ta\<rfloor>` iec Invoke a n wtext sub
      have "check_instr (ins ! pc) P h' stk loc C M pc Frs"
        by(auto simp add: is_Ref_def intro!: external_WT'.intros)
      with check meth have "check P (xcp, h', frs)" by(simp add: check_def)
      ultimately have "P,t \<turnstile> Normal (xcp, h', frs) -extTA2JVM P TA'-jvmd\<rightarrow> Normal (extRet2JVM n h''' stk loc C M pc Frs va')"
	by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
      thus ?thesis by(cases TA') (fastsimp)
    next
      case MEnter
      with meth l exec have "hd stk \<noteq> Null" by(auto)
      with check meth MEnter obtain a where [simp]: "hd stk = Addr a"
	by(auto elim: is_AddrE simp add: check_def is_Ref_def)
      from meth exec have "(ta, xcp', h', frs') \<in> exec P t (xcp, h', frs)" by(simp add: MEnter)
      moreover from meth check MEnter have "check P (xcp, h', frs)" by(simp add: check_def)
      ultimately have "P,t \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
	by -(rule exec_1_d_NormalI, auto simp add: exec_d_def)
      thus ?thesis by(auto simp del: split_paired_Ex)
    qed(auto split: split_if_asm simp add: finfun_upd_apply ta_upd_simps split_beta)
  next
    assume "\<exists>t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    then obtain t where t: "Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by blast
    from join_hext[OF wf cs red t hext] show ?thesis by(auto simp del: split_paired_Ex)
  qed
  thus "\<exists>ta x' m'. mexecd P t ((xcp, frs), h') ta (x', m')" by(fastsimp)
qed


lemma can_sync_devreserp_d:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and cl': "execd_mthr.can_sync P t (xcp, frs) h' L" 
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
  and hext: "hext h h'"
  and hconf': "hconf h'"
  shows "\<exists>L'\<subseteq>L. execd_mthr.can_sync P t (xcp, frs) h L'"
proof -
  from cl' obtain ta xcp' frs' m'
    where red: "P,t \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and L: "L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
    by -(erule execd_mthr.can_syncE, auto)
  then obtain f Frs
    where check: "check P (xcp, h', frs)"
    and exec: "(ta, xcp', m', frs') \<in> exec P t (xcp, h', frs)"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE simp add: finfun_upd_apply)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)
  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "hconf h" and
    tconf:  "P,h \<turnstile> t \<surd>t" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs" 
    by (fastsimp simp add: correct_state_def dest: sees_method_fun)
  from cs have "exec P t (xcp, h, f # Frs) \<noteq> {}"
    by(auto dest!: progress[OF wf] simp add: exec_1_iff)
  with no_type_error[OF wf cs] have check': "check P (xcp, h, frs)"
    by(auto simp add: exec_d_def split: split_if_asm)
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
  from tconf hext have tconf': "P,h' \<turnstile> t \<surd>t" by(rule tconf_hext_mono)
  show ?thesis
  proof(cases xcp)
    case (Some a)[simp]
    with exec have [simp]: "m' = h'" by(auto)
    from `\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>` obtain D where "typeof_addr h a = \<lfloor>Class D\<rfloor>"
      by(auto simp add: correct_state_def)
    with hext have "cname_of h a = cname_of h' a" by(auto dest: hext_objD simp add: cname_of_def)
    with exec have "(ta, xcp', h, frs') \<in> exec P t (xcp, h, frs)" by auto
    moreover from check have "check P (xcp, h, frs)" by(simp add: check_def)
    ultimately have "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h, frs')"
      by -(rule exec_1_d_NormalI, simp only: exec_d_def if_True)
    with L have "execd_mthr.can_sync P t (xcp, frs) h L"
      by(auto intro: execd_mthr.can_syncI)
    thus ?thesis by auto
  next
    case None[simp]

    note [simp] = defs1 list_all2_Cons2

    from frame have ST: "P,h \<turnstile> stk [:\<le>] ST"
      and LT: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT"
      and pc: "pc < length ins" by simp_all
    from wf meth pc have wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
      by(rule wt_jvm_prog_impl_wt_instr)

    from `\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>`
    have "\<exists>ta \<sigma>'. P,t \<turnstile> (xcp, h, f # Frs) -ta-jvm\<rightarrow> \<sigma>'"
      by(auto dest: progress[OF wf] simp del: correct_state_def split_paired_Ex)
    with exec meth have "\<exists>ta' \<sigma>'. (ta', \<sigma>') \<in> exec P t (xcp, h, frs) \<and> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>} \<subseteq> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
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
	with a obtain ao Ta where Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
	  by(auto simp add: conf_def)
	from hext Ta have Ta': "typeof_addr h' a = \<lfloor>Ta\<rfloor>" by(rule typeof_addr_hext_mono)
	show ?thesis
	proof(cases "is_external_call P Ta M'")
	  case False
	  with exec meth a Ta Ta' Invoke n show ?thesis by(simp add: split_beta)
	next
	  case True
	  with exec meth a Ta Ta' Invoke n
	  obtain ta' va h'' where ta': "ta = extTA2JVM P ta'"
	    and va: "(xcp', m', frs') = extRet2JVM n h'' stk loc C M pc Frs va"
	    and exec': "(ta', va, h'') \<in> red_external_aggr P t a M' (rev (take n stk)) h'"
	    by(fastsimp)
	  from va have [simp]: "h'' = m'" by(cases va) simp_all
	  note Ta moreover from check True Invoke Ta meth a n Ta'
	  obtain U where "P,h' \<turnstile> a\<bullet>M'(rev (take n stk)) : U" by(auto simp add: check_def)
	  with wfp exec' tconf' have red: "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h'\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
	    by(simp add: WT_red_external_list_conv)
	  from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" by(rule list_all2_takeI)
	  then obtain Ts where "map typeof\<^bsub>h\<^esub> (take n stk) = map Some Ts"
	    by(auto simp add: confs_conv_map)
	  hence "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some (rev Ts)" by(simp only: rev_map[symmetric])
	  moreover hence "map typeof\<^bsub>h'\<^esub> (rev (take n stk)) = map Some (rev Ts)" using hext by(rule map_typeof_hext_mono)
	  with `P,h' \<turnstile> a\<bullet>M'(rev (take n stk)) : U` Ta' obtain Us where "P \<turnstile> Ta\<bullet>M'(Us) :: U" "P \<turnstile> rev Ts [\<le>] Us"
	    by(auto simp add: external_WT'_iff)
	  ultimately have "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : U" by(rule external_WT'.intros)
          from red_external_wt_hconf_hext[OF wfp red hext this tconf hconf]
	  obtain ta'' va' h''' where "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h\<rangle> -ta''\<rightarrow>ext \<langle>va',h'''\<rangle>"
	    and ta'': "collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>" "{t. Join t \<in> set \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>}"
            by auto
	  with True a Ta Invoke meth Ta' n
	  have "(extTA2JVM P ta'', extRet2JVM n h''' stk loc C M pc Frs va') \<in> exec P t (xcp, h, frs)"
	    by(force intro: red_external_imp_red_external_aggr simp del: split_paired_Ex)
	  with ta'' ta' show ?thesis by(fastsimp simp del: split_paired_Ex)
	qed
      qed
    qed(auto split: split_if_asm simp add: split_beta ta_upd_simps exec_1_iff simp del: split_paired_Ex)
    with check' have "\<exists>ta' \<sigma>'. P,t \<turnstile> Normal (xcp, h, frs) -ta'-jvmd\<rightarrow> Normal \<sigma>' \<and> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>} \<subseteq> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
      apply clarify
      apply(rule exI conjI)+
      apply(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
      done
    with L show ?thesis
      apply -
      apply(erule exE conjE|rule exI conjI)+
      prefer 2
      apply(rule_tac x'="(fst \<sigma>', snd (snd \<sigma>'))" and m'="fst (snd \<sigma>')" in execd_mthr.can_syncI)
      apply auto
      done
  qed
qed

end

context JVM_typesafe begin

lemma execd_preserve_deadlocked:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and lto: "lock_thread_ok (locks S) (thr S)"
  and wto: "wset_thread_ok (wset S) (thr S)"
  and cs: "correct_state_ts \<Phi> (thr S) (shr S)"
  shows "preserve_deadlocked JVM_final (mexecd P) convert_RA S"
proof(unfold_locales)
  fix tta s t' ta' s' t x ln LT
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "execd_mthr.can_sync P t x (shr s) LT"
    and LTnempty: "LT \<noteq> {}"
  moreover obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have ml: "execd_mthr.can_sync P t (xcp, frs) (shr s) LT" by simp
  moreover from cs Red have cs': "correct_state_ts \<Phi> (thr s) (shr s)"
    by-(rule preserves_correct_state_d[OF wf])
  with tst have "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>"
    by(auto dest: ts_okD)
  moreover from red have "hext (shr s) (shr s')" by(rule execd_hext)
  moreover from wf red cs' have "correct_state_ts \<Phi> (thr s') (shr s')"
    by(rule lifting_wf.redT_preserves[OF lifting_wf_correct_state_d])
  from red tst have "thr s' t \<noteq> None"
    by(cases s)(cases s', rule notI, auto dest: execd_mthr.redT_thread_not_disappear)
  with `correct_state_ts \<Phi> (thr s') (shr s')` have "hconf (shr s')"
    by(auto dest: ts_okD simp add: correct_state_def)
  ultimately have "execd_mthr.must_sync P t (xcp, frs) (shr s')" using LTnempty
    by-(rule must_sync_preserved_d[OF wf])
  thus "execd_mthr.must_sync P t x (shr s')" by simp
next
  fix tta s t' ta' s' t x ln L
  assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
    and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "execd_mthr.can_sync P t x (shr s') L"
  moreover obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have ml: "execd_mthr.can_sync P t (xcp, frs) (shr s') L" by simp
  moreover from cs Red have cs': "correct_state_ts \<Phi> (thr s) (shr s)"
    by-(rule preserves_correct_state_d[OF wf])
  with tst have "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>"
    by(auto dest: ts_okD)
  moreover from red have "hext (shr s) (shr s')" by(rule execd_hext)
  moreover from red tst have "thr s' t \<noteq> None"
    by(cases s)(cases s', rule notI, auto dest: execd_mthr.redT_thread_not_disappear)
  from red cs' have "correct_state_ts \<Phi> (thr s') (shr s')"
    by(rule lifting_wf.redT_preserves[OF lifting_wf_correct_state_d[OF wf]])
  with `thr s' t \<noteq> None` have "hconf (shr s')"
    by(auto dest: ts_okD simp add: correct_state_def)
  ultimately have "\<exists>L' \<subseteq> L. execd_mthr.can_sync P t (xcp, frs) (shr s) L'"
    by-(rule can_sync_devreserp_d[OF wf])
  thus "\<exists>L' \<subseteq> L. execd_mthr.can_sync P t x (shr s) L'" by simp
qed fact+

end


text {* and now everything again for the aggresive VM *}

context JVM_heap_conf_base' begin

lemma must_lock_d_eq_must_lock:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<Phi> \<turnstile> t: (xcp, h, frs) \<surd> \<rbrakk>
  \<Longrightarrow> execd_mthr.must_sync P t (xcp, frs) h = exec_mthr.must_sync P t (xcp, frs) h"
apply(rule iffI)
 apply(rule exec_mthr.must_syncI)
 apply(erule execd_mthr.must_syncE)
 apply(simp only: mexec_eq_mexecd)
 apply(blast)
apply(rule execd_mthr.must_syncI)
apply(erule exec_mthr.must_syncE)
apply(simp only: mexec_eq_mexecd[symmetric])
apply(blast)
done

lemma can_lock_d_eq_can_lock:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<Phi> \<turnstile> t: (xcp, h, frs) \<surd> \<rbrakk>
  \<Longrightarrow> execd_mthr.can_sync P t (xcp, frs) h L = exec_mthr.can_sync P t (xcp, frs) h L"
apply(rule iffI)
 apply(erule execd_mthr.can_syncE)
 apply(rule exec_mthr.can_syncI)
   apply(simp only: mexec_eq_mexecd)
  apply(assumption)+
apply(erule exec_mthr.can_syncE)
apply(rule execd_mthr.can_syncI)
 by(simp only: mexec_eq_mexecd)

end

context JVM_typesafe begin

lemma exec_preserve_deadlocked:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and lto: "lock_thread_ok (locks S) (thr S)"
  and wto: "wset_thread_ok (wset S) (thr S)"
  and cs: "correct_state_ts \<Phi> (thr S) (shr S)"
  shows "preserve_deadlocked JVM_final (mexec P) convert_RA S"
proof -
  interpret preserve_deadlocked JVM_final "mexecd P" convert_RA S
    by(rule execd_preserve_deadlocked) fact+

  { fix tta s t' ta' s' t x ln
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s"
      and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvm\<^esub> s'"
      and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from wf cs Red have Redd: "P \<turnstile> S -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s"
      by(simp add: mExecT_eq_mExecdT)
    moreover from Red cs have css: "correct_state_ts \<Phi> (thr s) (shr s)" 
      by-(rule preserves_correct_state[OF wf])
    with red have redd: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
      by(simp add: mexecT_eq_mexecdT[OF wf])
    from css tst have cst: "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from redd have cst': "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>"
    proof(cases rule: execd_mthr.redT_elims)
      case acquire with cst show ?thesis by simp
    next
      case (normal X X' M' ws')
      obtain XCP FRS where X [simp]: "X = (XCP, FRS)" by(cases X, auto)
      obtain XCP' FRS' where X' [simp]: "X' = (XCP', FRS')" by(cases X', auto)
      from `mexecd P t' (X, shr s) ta' (X', M')`
      have "P,t' \<turnstile> Normal (XCP, shr s, FRS) -ta'-jvmd\<rightarrow> Normal (XCP', M', FRS')" by simp
      moreover from `thr s t' = \<lfloor>(X, no_wait_locks)\<rfloor>` css
      have "\<Phi> \<turnstile> t': (XCP, shr s, FRS) \<surd>" by(auto dest: ts_okD)
      ultimately have "\<Phi> \<turnstile> t': (XCP, M', FRS) \<surd>" by -(rule correct_state_heap_change[OF wf])
      moreover from lifting_wf.redT_updTs_preserves[OF lifting_wf_correct_state_d[OF wf] css, OF `mexecd P t' (X, shr s) ta' (X', M')` `thr s t' = \<lfloor>(X, no_wait_locks)\<rfloor>`, of no_wait_locks] `thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>`
      have "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t' \<mapsto> (X', no_wait_locks))) M'" by simp
      ultimately have "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>) M'"
        using `thr s t' = \<lfloor>(X, no_wait_locks)\<rfloor>` `thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>`
        apply(auto intro!: ts_okI dest: ts_okD)
        apply(case_tac "t=t'")
         apply(fastsimp dest: redT_updTs_Some)
        apply(drule_tac t=t in ts_okD, fastsimp+)
        done
      hence "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>) (shr s')" 
        using `s' = (redT_updLs (locks s) t' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>, (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t' \<mapsto> (X', redT_updLns (locks s) t' no_wait_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>)), M'), ws')`
        by simp
      moreover from tst `thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>`
      have "redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>(x, ln)\<rfloor>" by(auto intro: redT_updTs_Some)
      ultimately show ?thesis by(auto dest: ts_okD)
    qed
    { fix L
      assume "exec_mthr.can_sync P t x (shr s) L"
	and L: "L \<noteq> {}"
      hence ml: "exec_mthr.can_sync P t (xcp, frs) (shr s) L" by simp
      with cst have "execd_mthr.can_sync P t (xcp, frs) (shr s) L"
	by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with Redd redd tst have "execd_mthr.must_sync P t x (shr s')"
        unfolding x using L by(rule can_lock_preserved)
      with cst' have "exec_mthr.must_sync P t x (shr s')"
	by(auto dest: must_lock_d_eq_must_lock[OF wf]) }
    note ml = this
    { fix L
      assume "exec_mthr.can_sync P t x (shr s') L"
      hence cl: "exec_mthr.can_sync P t (xcp, frs) (shr s') L" by simp
      with cst' have "execd_mthr.can_sync P t (xcp, frs) (shr s') L"
	by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with Redd redd tst
      have "\<exists>L' \<subseteq> L. execd_mthr.can_sync P t x (shr s) L'"
        unfolding x by(rule can_lock_devreserp)
      then obtain L' where "execd_mthr.can_sync P t x (shr s) L'" 
	and L': "L'\<subseteq> L" by blast
      with cst have "exec_mthr.can_sync P t x (shr s) L'"
	by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with L' have "\<exists>L' \<subseteq> L. exec_mthr.can_sync P t x (shr s) L'"
	by(blast) }
    note this ml }
  thus ?thesis using lto wto by(unfold_locales)
qed

end

end
