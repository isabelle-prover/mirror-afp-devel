(*  Title:      JinjaThreads/Compiler/Correctness2Threaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of Stage 2: The multithreaded setting} *}

theory Correctness2Threaded imports J1JVM JVMJ1 Correctness1Threaded "../JVM/JVMThreaded" begin

lemma \<tau>Exec_1_rtranclpD:
  "\<tau>Exec_1 P (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> (\<lambda>((xcp, frs), h) ((xcp', frs'), h'). exec_1' (compP2 P) (xcp, h, frs) \<epsilon> (xcp', h', frs') \<and> \<tau>Move2 P (xcp, h, frs))^** ((xcp, frs), h) ((xcp', frs'), h')"
apply(induct s\<equiv>"(xcp,h,frs)" s'\<equiv>"(xcp', h', frs')" arbitrary: xcp h frs xcp' h' frs' rule: \<tau>Exec_1.induct)
apply(fastsimp intro: rtranclp.rtrancl_into_rtrancl)+
done

lemma \<tau>Red1_rtranclpD:
  "\<tau>Red1 P h s s' \<Longrightarrow> (\<lambda>((ex, exs), h) ((ex', exs'), h'). P \<turnstile>1 \<langle>ex/exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>ex'/exs', h'\<rangle> \<and> \<tau>Move1 (ex, exs))^** (s, h) (s', h)"
apply(induct rule: \<tau>Red1.induct)
apply(auto intro: rtranclp.rtrancl_into_rtrancl)
done

lemma exec_instr_\<tau>move2_taD:
  "\<lbrakk> \<tau>move2 e pc None; pc < length (compE2 e);
    (ta, xcp', h2', frs') \<in> set (exec_instr (compE2 e ! pc) (compP2 P) h stk loc C M pc' frs)\<rbrakk>
  \<Longrightarrow> ta = \<epsilon>"

  and exec_instr_\<tau>moves2_taD:
  "\<lbrakk> \<tau>moves2 es pc None; pc < length (compEs2 es);
    (ta, xcp', h2', frs') \<in> set (exec_instr (compEs2 es ! pc) (compP2 P) h stk loc C M pc' frs)\<rbrakk>
  \<Longrightarrow> ta = \<epsilon>"
apply(induct e pc xcp\<equiv>"None::addr option" and es pc xcp\<equiv>"None::addr option" rule: \<tau>move2_\<tau>moves2.inducts)
apply(auto simp add: nth_Cons split: split_if_asm dest: \<tau>move2_pc_length_compE2 \<tau>moves2_pc_length_compEs2)
done

lemma bisim1_list1_has_methodD: "bisim1_list1 P h ex exs xcp ((stk, loc, C, M, pc) # frs) \<Longrightarrow> P \<turnstile> C has M"
by(fastsimp elim!: bisim1_list1.cases intro: has_methodI)

declare compP_has_method [simp]

abbreviation mexec_1' :: "jvm_prog \<Rightarrow> (addr,addr,addr option \<times> frame list,heap,addr) semantics"
where "mexec_1' P \<equiv> \<lambda>((xcp, frs), h) ta ((xcp', frs'), h'). exec_1' P (xcp, h, frs) ta (xcp', h', frs')"

abbreviation \<tau>MOVE1 :: "(((expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list) \<times> heap,
                       (addr,addr,(expr1 \<times> locals1) \<times> (expr1 \<times> locals1) list,heap,addr) thread_action) trsys"
where "\<tau>MOVE1 \<equiv> \<lambda>(exexs, h) ta s. \<tau>Move1 exexs \<and> ta = \<epsilon>"

abbreviation \<tau>MOVE2 :: "J1_prog \<Rightarrow> ((addr option \<times> frame list) \<times> heap,
                                 (addr,addr,addr option \<times> frame list,heap,addr) thread_action) trsys"
where "\<tau>MOVE2 P \<equiv> \<lambda>((xcp, frs), h) ta s. \<tau>Move2 P (xcp, h, frs) \<and> ta = \<epsilon>"

interpretation Red1_exec1_wbase:
  weak_bisimulation_base "mred1 P" "mexec_1' (compP2 P)" "wbisim1 P" "ta_bisim (wbisim1 P)" \<tau>MOVE1 "\<tau>MOVE2 P"
.

lemma Red1_exec1_weak_bisim:
  assumes wf: "wf_J1_prog P"
  shows "weak_bisimulation (mred1 P) (mexec_1' (compP2 P)) (wbisim1 P) (ta_bisim (wbisim1 P)) \<tau>MOVE1 (\<tau>MOVE2 P)"
proof
  fix s1 s2 tl1 s1'
  assume "wbisim1 P s1 s2" and "mred1 P s1 tl1 s1'" and "\<tau>MOVE1 s1 tl1 s1'"
  moreover obtain e xs exs h where s1: "s1 = (((e, xs), exs), h)" by(cases s1) auto
  moreover obtain e' xs' exs' h1' where s1': "s1' = (((e', xs'), exs'), h1')" by(cases s1') auto
  moreover obtain xcp frs h2 where s2: "s2 = ((xcp, frs), h2)" by(cases s2) auto
  ultimately have [simp]: "h2 = h" "tl1 = \<epsilon>" and red: "P \<turnstile>1 \<langle>(e, xs)/exs,h\<rangle> -\<epsilon>\<rightarrow> \<langle>(e', xs')/exs',h1'\<rangle>"
    and \<tau>: "\<tau>Move1 ((e, xs), exs)" and bisim: "bisim1_list1 P h (e, xs) exs xcp frs" by(auto)
  from red \<tau> have h1' [simp]: "h1' = h" by(auto dest: \<tau>move1_heap_unchanged elim!: Red1.cases)
  from exec_1_simulates_Red1_\<tau>[OF wf red[unfolded h1'] bisim \<tau>] obtain xcp' frs'
    where exec: "\<tau>Exec_1 P (xcp, h, frs) (xcp', h, frs')"
    and bisim': "bisim1_list1 P h (e', xs') exs' xcp' frs'" by blast
  have "(\<lambda>s2 s2'. mexec_1' (compP2 P) s2 \<epsilon> s2' \<and> \<tau>MOVE2 P s2 \<epsilon> s2')\<^sup>*\<^sup>* ((xcp, frs), h) ((xcp', frs'), h)"
    using \<tau>Exec_1_rtranclpD[OF exec] by(simp add: split_def)
  thus "\<exists>s2'. \<tau>trsys.\<tau>moves (mexec_1' (compP2 P)) (\<tau>MOVE2 P) s2 s2' \<and> wbisim1 P s1' s2'"
    unfolding Red1_exec1_wbase.trsys2.\<tau>moves_def using bisim' s1 s1' s2 by auto
next
  fix s1 s2 tl2 s2'
  assume "wbisim1 P s1 s2" and "mexec_1' (compP2 P) s2 tl2 s2'" and "\<tau>MOVE2 P s2 tl2 s2'"
  moreover obtain e xs exs h1 where s1: "s1 = (((e, xs), exs), h1)" by(cases s1) auto
  moreover obtain xcp frs h where s2: "s2 = ((xcp, frs), h)" by(cases s2) auto
  moreover obtain xcp' frs' h2' where s2': "s2' = ((xcp', frs'), h2')" by(cases s2') auto
  ultimately have [simp]: "h1 = h" "tl2 = \<epsilon>" and exec: "exec_1' (compP2 P) (xcp, h, frs) \<epsilon> (xcp', h2', frs')"
    and \<tau>: "\<tau>Move2 P (xcp, h, frs)" and bisim: "bisim1_list1 P h (e, xs) exs xcp frs" by(auto)
  from \<tau>Red1_simulates_exec_1_\<tau>[OF wf exec bisim \<tau>]
  obtain e' xs' exs' where [simp]: "h2' = h"
    and red: "\<tau>Red1 P h ((e, xs), exs) ((e', xs'), exs')"
    and bisim': "bisim1_list1 P h (e', xs') exs' xcp' frs'" by blast
  have "(\<lambda>s1 s1'. mred1 P s1 \<epsilon> s1' \<and> \<tau>MOVE1 s1 \<epsilon> s1')\<^sup>*\<^sup>* (((e, xs), exs), h) (((e', xs'), exs'), h)"
    using \<tau>Red1_rtranclpD[OF red] by(simp add: split_def)
  thus "\<exists>s1'. \<tau>trsys.\<tau>moves (mred1 P) \<tau>MOVE1 s1 s1' \<and> wbisim1 P s1' s2'"
    unfolding Red1_exec1_wbase.trsys1.\<tau>moves_def using bisim' s1 s2 s2' by auto
next
  fix s1 s2 tl1 s1'
  assume "wbisim1 P s1 s2" and "mred1 P s1 tl1 s1'" and "\<not> \<tau>MOVE1 s1 tl1 s1'"
  moreover obtain e xs exs h where s1: "s1 = (((e, xs), exs), h)" by(cases s1) auto
  moreover obtain e' xs' exs' h1' where s1': "s1' = (((e', xs'), exs'), h1')" by(cases s1') auto
  moreover obtain xcp frs h2 where s2: "s2 = ((xcp, frs), h2)" by(cases s2) auto
  ultimately have [simp]: "h2 = h"  and red: "P \<turnstile>1 \<langle>(e, xs)/exs,h\<rangle> -tl1\<rightarrow> \<langle>(e', xs')/exs',h1'\<rangle>"
    and \<tau>: "\<not> \<tau>Move1 ((e, xs), exs)" and bisim: "bisim1_list1 P h (e, xs) exs xcp frs"
    by(auto elim!: Red1.cases dest: red1_\<tau>_taD)
  from exec_1_simulates_Red1_not_\<tau>[OF wf red bisim \<tau>] obtain ta' xcp' frs' xcp'' frs''
    where exec1: "\<tau>Exec_1 P (xcp, h, frs) (xcp', h, frs')"
    and exec2: "exec_1' (compP2 P) (xcp', h, frs') ta' (xcp'', h1', frs'')"
    and \<tau>': "\<not> \<tau>Move2 P (xcp', h, frs')"
    and bisim': "bisim1_list1 P h1' (e', xs') exs' xcp'' frs''"
    and ta': "ta_bisim (wbisim1 P) tl1 ta'" by blast
  have "(\<lambda>s2 s2'. mexec_1' (compP2 P) s2 \<epsilon> s2' \<and> \<tau>MOVE2 P s2 \<epsilon> s2')\<^sup>*\<^sup>* ((xcp, frs), h) ((xcp', frs'), h)"
    using \<tau>Exec_1_rtranclpD[OF exec1] by(simp add: split_def)
  thus "\<exists>s2' s2'' tl2. \<tau>trsys.\<tau>moves (mexec_1' (compP2 P)) (\<tau>MOVE2 P) s2 s2' \<and> 
                                mexec_1' (compP2 P) s2' tl2 s2'' \<and> \<not> \<tau>MOVE2 P s2' tl2 s2'' \<and>
                                wbisim1 P s1' s2'' \<and> ta_bisim (wbisim1 P) tl1 tl2"
    using bisim' exec2 \<tau>' s1 s1' s2 ta' unfolding `h2 = h` Red1_exec1_wbase.trsys2.\<tau>moves_def
    apply(subst (1 2) split_paired_Ex)
    apply(subst (1 2) split_paired_Ex)
    by clarify ((rule exI conjI|assumption)+, auto)
next
  fix s1 s2 tl2 s2'
  assume "wbisim1 P s1 s2" and "mexec_1' (compP2 P) s2 tl2 s2'" and "\<not> \<tau>MOVE2 P s2 tl2 s2'"
  moreover obtain e xs exs h1 where s1: "s1 = (((e, xs), exs), h1)" by(cases s1) auto
  moreover obtain xcp frs h where s2: "s2 = ((xcp, frs), h)" by(cases s2) auto
  moreover obtain xcp' frs' h2' where s2': "s2' = ((xcp', frs'), h2')" by(cases s2') auto
  ultimately have [simp]: "h1 = h"  and exec: "exec_1' (compP2 P) (xcp, h, frs) tl2 (xcp', h2', frs')"
    and \<tau>: "\<not> \<tau>Move2 P (xcp, h, frs)" and bisim: "bisim1_list1 P h (e, xs) exs xcp frs"
    apply auto
    apply(erule exec_1'.cases, simp_all add: split_paired_all)
    apply(frule bisim1_list1_has_methodD,clarsimp simp add: has_method_def compP2_def compMb2_def split: split_if_asm, drule (1) exec_instr_\<tau>move2_taD, simp add: compP2_def compMb2_def, simp)
    done
  from \<tau>Red1_simulates_exec_1_not_\<tau>[OF wf exec bisim \<tau>] obtain e' xs' exs' ta' e'' xs'' exs''
    where red1: "\<tau>Red1 P h ((e, xs), exs) ((e', xs'), exs')"
    and red2: "P \<turnstile>1 \<langle>(e', xs')/exs',h\<rangle> -ta'\<rightarrow> \<langle>(e'', xs'')/exs'',h2'\<rangle>"
    and \<tau>': "\<not> \<tau>Move1 ((e', xs'), exs')" and ta': "ta_bisim (wbisim1 P) ta' tl2"
    and bisim': "bisim1_list1 P h2' (e'', xs'') exs'' xcp' frs'" by blast
  from \<tau>Red1_rtranclpD[OF red1] have "(\<lambda>s1 s1'. mred1 P s1 \<epsilon> s1' \<and> \<tau>MOVE1 s1 \<epsilon> s1')\<^sup>*\<^sup>* (((e, xs), exs), h) (((e', xs'), exs'), h)"
    by(simp add: split_def)
  thus "\<exists>s1' s1'' tl1. \<tau>trsys.\<tau>moves (mred1 P) \<tau>MOVE1 s1 s1' \<and> mred1 P s1' tl1 s1'' \<and>
                                 \<not> \<tau>MOVE1 s1' tl1 s1'' \<and> wbisim1 P s1'' s2' \<and> ta_bisim (wbisim1 P) tl1 tl2"
    using bisim' red2 \<tau>' s1 s2 s2' `h1 = h` ta' unfolding Red1_exec1_wbase.trsys1.\<tau>moves_def
    apply -
    apply(rule exI[where x="(((e', xs'), exs'), h)"])
    apply(rule exI[where x="(((e'', xs''), exs''), h2')"])
    apply(rule exI[where x="ta'"])
    apply auto
    done
qed

lemma Red1_final_wf: "final_thread_wf final_expr1 (mred1 P)"
by(unfold_locales)(auto elim!: Red1.cases final.cases)

interpretation Red1_final_wf: final_thread_wf final_expr1 "mred1 P"
by(rule Red1_final_wf)

lemma exec1_mthr: "multithreaded (mexec_1' P)"
apply(unfold_locales)
apply(auto)
apply(erule exec_1'.cases)
apply(auto)
apply(case_tac "instrs_of P C M ! pc")
apply(fastsimp split: split_if_asm simp add: red_external_list_conv[symmetric] dest: red_ext_new_thread_heap)+
done

interpretation exec1_mthr: multithreaded JVM_final "mexec_1' P"
by(rule exec1_mthr)

lemma exec1_final_wf: "final_thread_wf JVM_final (mexec_1' P)"
by(unfold_locales)(auto elim: exec_1'.cases)

interpretation exec1_final_wf: final_thread_wf JVM_final "mexec_1' P"
by(rule exec1_final_wf)

lemma Red1_exec1_FWbase: "FWbisimulation_base (mred1 P) (mexec_1' (compP2 P))"
by unfold_locales

interpretation Red1_exec1_FWbase:
  FWbisimulation_base final_expr1 "mred1 P" JVM_final "mexec_1' (compP2 P)" "wbisim1 P"
by(rule Red1_exec1_FWbase)

lemma \<tau>exec_1_heap_unchanged:
  assumes exec: "exec_1' (compP2 P) (xcp, h, frs) \<epsilon> (xcp', h', frs')"
  and bl: "bisim1_list1 P h ex exs xcp frs"
  and \<tau>: "\<tau>Move2 P (xcp, h, frs)"
  shows "h' = h"
using bl exec \<tau>
by(cases)(auto elim!: exec_1'.cases simp add: compP2_def compMb2_def split: split_if_asm elim: exec_meth_\<tau>_heap_unchanged)

lemma exec_1_changes: 
  assumes exec: "exec_1' (compP2 P) (xcp, h, frs) \<epsilon> (xcp, h, frs)"
  and bl: "bisim1_list1 P m2 ex exs xcp frs"
  shows False
using bl
proof cases
  case (bl1_Normal C M Ts EXS FRS T body D EX stk loc pc XCP)
  from `P \<turnstile> C sees M: Ts\<rightarrow>T = body in D` `frs = (stk, loc, C, M, pc) # FRS` `xcp = XCP` exec
  show ?thesis
    apply(auto elim!: exec_1'.cases simp add: split_beta neq_Nil_conv split: split_if_asm)
    apply(cases "compE2 body ! pc", auto split: split_if_asm sum.split_asm simp add: split_beta neq_Nil_conv compP2_def compMb2_def dest: compE1_Goto_not_same)
    done
qed(insert exec, auto elim!: exec_1'.cases)

lemma Red1_hext_incr: "P \<turnstile>1 \<langle>ex/exs,h\<rangle> -ta\<rightarrow> \<langle>ex'/exs',h'\<rangle> \<Longrightarrow> hext h h'"
by(auto elim!: Red1.cases dest: red1_hext_incr)

interpretation exec1_\<tau>mthr: \<tau>multithreaded JVM_final "mexec_1' (compP2 P)" "\<tau>MOVE2 P"
by(unfold_locales)

interpretation Red1_\<tau>mthr: \<tau>multithreaded final_expr1 "mred1 P" \<tau>MOVE1
by(unfold_locales)

interpretation Red1_exec1_FWwbase:
  FWweak_bisimulation_base final_expr1 "mred1 P" JVM_final "mexec_1' (compP2 P)" "wbisim1 P" \<tau>MOVE1 "\<tau>MOVE2 P"
by(unfold_locales)


lemma Red1_\<tau>mthr_wf: "\<tau>multithreaded_wf (mred1 P) \<tau>MOVE1 wfs"
proof
  fix x1 m1 ta1 x1' m1'
  assume "mred1 P (x1, m1) ta1 (x1', m1')" and "\<tau>MOVE1 (x1, m1) ta1 (x1', m1')"
  thus "m1 = m1'" by(cases x1, cases x1')(fastsimp elim!: Red1.cases dest: \<tau>move1_heap_unchanged)
next
  fix s assume "mred1 P s \<epsilon> s"
  thus "\<tau>MOVE1 s \<epsilon> s" by(cases s)(auto elim!: Red1.cases dest: red1_changes)
qed simp

interpretation Red1_\<tau>mthr_wf:
  \<tau>multithreaded_wf final_expr1 "mred1 P" \<tau>MOVE1 wfs
by(rule Red1_\<tau>mthr_wf)

lemma exec1_\<tau>mthr_wf: "\<tau>multithreaded_wf (mexec_1' (compP2 P)) (\<tau>MOVE2 P) (\<lambda>s2. \<exists>s1. wbisim1 P s1 s2)"
proof
  fix x2 m2 ta2 x2' m2'
  assume "\<exists>s1. wbisim1 P s1 (x2, m2)" "mexec_1' (compP2 P) (x2, m2) ta2 (x2', m2')" and "\<tau>MOVE2 P (x2, m2) ta2 (x2', m2')"
  thus "m2 = m2'" by(cases x2, cases x2')(auto dest: \<tau>exec_1_heap_unchanged)
next
  fix s assume "\<exists>s1. wbisim1 P s1 s" "mexec_1' (compP2 P) s \<epsilon> s"
  thus "\<tau>MOVE2 P s \<epsilon> s" by(cases s)(auto dest: exec_1_changes)
qed simp

interpretation exec1_\<tau>mthr_wf:
  \<tau>multithreaded_wf JVM_final "mexec_1' (compP2 P)" "\<tau>MOVE2 P" "\<lambda>s2. \<exists>s1. wbisim1 P s1 s2"
by(rule exec1_\<tau>mthr_wf)

lemma wbisim1_final_eq:
  "wbisim1 P (exs, h) (\<sigma>, h') \<Longrightarrow> final_expr1 exs \<longleftrightarrow> JVM_final \<sigma>"
apply(cases exs, cases \<sigma>)
apply(auto elim: bisim1_list1.cases bisim1_list.cases)
done

theorem Red1_exec1_FWwbisim:
  assumes wf: "wf_J1_prog P"
  shows "FWweak_bisimulation final_expr1 (mred1 P) JVM_final (mexec_1' (compP2 P)) (wbisim1 P) \<tau>MOVE1 (\<tau>MOVE2 P)"
proof -
  let ?exec = "mexec_1' (compP2 P)"
  let ?\<tau>exec = "(\<lambda>s2 s2'. ?exec s2 \<epsilon> s2' \<and> \<tau>MOVE2 P s2 \<epsilon> s2')\<^sup>*\<^sup>*"
  let ?\<tau>red = "(\<lambda>s1 s1'. mred1 P s1 \<epsilon> s1' \<and> \<tau>MOVE1 s1 \<epsilon> s1')\<^sup>*\<^sup>*"
  interpret weak_bisimulation "mred1 P" ?exec "wbisim1 P" "ta_bisim (wbisim1 P)" \<tau>MOVE1 "\<tau>MOVE2 P"
    by(intro Red1_exec1_weak_bisim wf)+
  show ?thesis
  proof
    fix x1 m1 x2 m2
    assume wb: "wbisim1 P (x1, m1) (x2, m2)" 
    thus "final_expr1 x1 = JVM_final x2" by(rule wbisim1_final_eq)
  next
    fix x m1 xx m2 x1 x2 x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume b: "wbisim1 P (x, m1) (xx, m2)" and "wbisim1 P (x1, m1) (x2, m2)"
      and "?\<tau>red (x1, m1) (x1', m1)"
      and red: "mred1 P (x1', m1) ta1 (x1'', m1')"
      and "\<not> \<tau>MOVE1 (x1', m1) ta1 (x1'', m1')"
      and "?\<tau>exec (x2, m2) (x2', m2)"
      and "?exec (x2', m2) ta2 (x2'', m2')"
      and "\<not> \<tau>MOVE2 P (x2', m2) ta2 (x2'', m2')"
      and b2: "wbisim1 P (x1'', m1') (x2'', m2')"
    from red have "hext m1 m1'" by(auto simp add: split_beta intro: Red1_hext_incr)
    moreover from b2 have "m1' = m2'" by(cases x1'', cases x2'') simp
    moreover from b2 have "P \<turnstile> m2' \<surd>" by(cases x1'', cases x2'')(auto elim: bisim1_list1.cases)
    moreover from b have "preallocated m2" by(cases x, cases xx)(auto elim!: bisim1_list1.cases simp add: hconf_def)
    ultimately show "wbisim1 P (x, m1') (xx, m2')" using b 
      apply(cases x, cases xx, clarsimp)
      apply(erule bisim1_list1.cases)
      apply(fastsimp intro: bisim1_list1.intros elim: bisim1_list_hext_mono bisim1_hext_mono exsconf_hext_mono)
      apply(fastsimp intro: bisim1_list1.intros exsconfI elim: bisim1_list_hext_mono bisim1_hext_mono exsconf_hext_mono WTrt1_hext_mono lconf1_hext_mono)+
      done
  qed
qed

end