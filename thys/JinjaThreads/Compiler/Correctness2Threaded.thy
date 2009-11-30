(*  Title:      JinjaThreads/Compiler/Correctness2Threaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of Stage 2: The multithreaded setting} *}

theory Correctness2Threaded
imports
  J1JVM
  JVMJ1
  Correctness1Threaded
  "../JVM/JVMThreaded"
  "../BV/BVProgressThreaded"
begin

abbreviation \<tau>MOVE2 :: "jvm_prog \<Rightarrow> ((addr option \<times> frame list) \<times> heap, jvm_thread_action) trsys" -- "Move to JVMTau"
where "\<tau>MOVE2 P \<equiv> \<lambda>((xcp, frs), h) ta s. \<tau>Move2 P (xcp, h, frs) \<and> ta = \<epsilon>"

lemma Red1_hext_incr: "P \<turnstile>1 \<langle>ex/exs,h\<rangle> -ta\<rightarrow> \<langle>ex'/exs',h'\<rangle> \<Longrightarrow> hext h h'" -- "Move to J1"
by(auto elim!: Red1.cases dest: red1_hext_incr)

declare Listn.lesub_list_impl_same_size[simp del]
declare listE_length [simp del]

lemma exec_instr_\<tau>move2_taD:
  "\<lbrakk> \<tau>move2 P h stk e pc None; (ta, xcp', h2', frs') \<in> set (exec_instr (compE2 e ! pc) (compP2 P) h stk loc C M pc' frs)\<rbrakk>
  \<Longrightarrow> ta = \<epsilon>"
by(cases "compE2 e ! pc")(auto simp add: \<tau>move2_iff compP2_def split: split_if_asm)

lemma exec_instr_\<tau>moves2_taD:
  "\<lbrakk> \<tau>moves2 P h stk es pc None; (ta, xcp', h2', frs') \<in> set (exec_instr (compEs2 es ! pc) (compP2 P) h stk loc C M pc' frs)\<rbrakk>
  \<Longrightarrow> ta = \<epsilon>"
by(cases "compEs2 es ! pc")(auto simp add: \<tau>moves2_iff compP2_def split: split_if_asm)

lemma bisim1_list1_has_methodD: "bisim1_list1 P h ex exs xcp ((stk, loc, C, M, pc) # frs) \<Longrightarrow> P \<turnstile> C has M"
by(fastsimp elim!: bisim1_list1.cases intro: has_methodI)

declare compP_has_method [simp]

interpretation Red1_exec_wbase:
  delay_bisimulation_base "mred1 P" "mexec (compP2 P)" "wbisim1 P" "ta_bisim (wbisim1 P)" "\<tau>MOVE1 P" "\<tau>MOVE2 (compP2 P)" for P
.

interpretation Red1_execd_wbase:
  delay_bisimulation_base "mred1 P" "mexecd (compP2 P)" "wbisim1 P" "ta_bisim (wbisim1 P)" "\<tau>MOVE1 P" "\<tau>MOVE2 (compP2 P)" for P
.

lemma \<tau>exec_1_d_silent_move:
  "\<tau>exec_1_d P (xcp, h, frs) (xcp', h', frs') \<Longrightarrow> \<tau>trsys.silent_move (mexecd P) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
apply(rule \<tau>trsys.silent_move.intros)
apply auto
apply(rule exec_1_d_NormalI)
apply(auto simp add: exec_1_iff exec_d_def)
done

lemma silent_move_\<tau>exec_1_d:
  "\<tau>trsys.silent_move (mexecd P) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')
  \<Longrightarrow> \<tau>exec_1_d P (xcp, h, frs) (xcp', h', frs')"
apply(erule \<tau>trsys.silent_move.cases)
apply clarsimp
apply(erule jvmd_NormalE)
apply(auto simp add: exec_1_iff)
done

lemma \<tau>Exec_1_dr_rtranclpD:
  "\<tau>Exec_1_dr P (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> \<tau>trsys.silent_moves (mexecd P) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
by(induct rule: rtranclp_induct3)(blast intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_1_d_silent_move)+

lemma \<tau>Exec_1_dt_tranclpD:
  "\<tau>Exec_1_dt P (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> \<tau>trsys.silent_movet (mexecd P) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
by(induct rule: tranclp_induct3)(blast intro: tranclp.trancl_into_trancl \<tau>exec_1_d_silent_move)+

lemma rtranclp_\<tau>Exec_1_dr:
  "\<tau>trsys.silent_moves (mexecd P) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')
  \<Longrightarrow> \<tau>Exec_1_dr P (xcp, h, frs) (xcp', h', frs')"
by(induct rule: rtranclp_induct[of _ "((ax, ay), az)" "((bx, by), bz)", split_rule, consumes 1])(blast intro: rtranclp.rtrancl_into_rtrancl silent_move_\<tau>exec_1_d)+

lemma tranclp_\<tau>Exec_1_dt:
  "\<tau>trsys.silent_movet (mexecd P) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')
  \<Longrightarrow> \<tau>Exec_1_dt P (xcp, h, frs) (xcp', h', frs')"
by(induct rule: tranclp_induct[of _ "((ax, ay), az)" "((bx, by), bz)", split_rule, consumes 1])(blast intro: tranclp.trancl_into_trancl silent_move_\<tau>exec_1_d)+

lemma \<tau>Exec_1_dr_conv_rtranclp:
  "\<tau>Exec_1_dr P (xcp, h, frs) (xcp', h', frs') = \<tau>trsys.silent_moves (mexecd P) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
by(blast intro: \<tau>Exec_1_dr_rtranclpD rtranclp_\<tau>Exec_1_dr)

lemma \<tau>Exec_1_dt_conv_tranclp:
  "\<tau>Exec_1_dt P (xcp, h, frs) (xcp', h', frs') = \<tau>trsys.silent_movet (mexecd P) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
by(blast intro: \<tau>Exec_1_dt_tranclpD tranclp_\<tau>Exec_1_dt)

lemma \<tau>Red1r_rtranclpD:
  "\<tau>Red1r P h s s' \<Longrightarrow> \<tau>trsys.silent_moves (mred1 P) (\<tau>MOVE1 P) (s, h) (s', h)"
apply(induct rule: rtranclp_induct)
apply(auto elim!: rtranclp.rtrancl_into_rtrancl intro: \<tau>trsys.silent_move.intros)
done

lemma \<tau>Red1t_tranclpD:
  "\<tau>Red1t P h s s' \<Longrightarrow> \<tau>trsys.silent_movet (mred1 P) (\<tau>MOVE1 P) (s, h) (s', h)"
apply(induct rule: tranclp_induct)
apply(rule tranclp.r_into_trancl)
apply(auto elim!: tranclp.trancl_into_trancl intro!: \<tau>trsys.silent_move.intros simp: \<tau>Red1_def)
done

lemma Red1_execd_weak_bisim:
  assumes wf: "wf_J1_prog P"
  shows "delay_bisimulation_measure (mred1 P) (mexecd (compP2 P)) (wbisim1 P) (ta_bisim (wbisim1 P)) (\<tau>MOVE1 P) (\<tau>MOVE2 (compP2 P)) (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e') (\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs')"
proof
  fix s1 s2 s1'
  assume "wbisim1 P s1 s2" and "\<tau>trsys.silent_move (mred1 P) (\<tau>MOVE1 P) s1 s1'" 
  moreover obtain e xs exs h where s1: "s1 = (((e, xs), exs), h)" by(cases s1) auto
  moreover obtain e' xs' exs' h1' where s1': "s1' = (((e', xs'), exs'), h1')" by(cases s1') auto
  moreover obtain xcp frs h2 where s2: "s2 = ((xcp, frs), h2)" by(cases s2) auto
  ultimately have [simp]: "h2 = h" and red: "P \<turnstile>1 \<langle>(e, xs)/exs,h\<rangle> -\<epsilon>\<rightarrow> \<langle>(e', xs')/exs',h1'\<rangle>"
    and \<tau>: "\<tau>Move1 P h ((e, xs), exs)" and bisim: "bisim1_list1 P h (e, xs) exs xcp frs" by(auto)
  from red \<tau> bisim have h1' [simp]: "h1' = h" by(auto dest: \<tau>move1_heap_unchanged elim!: Red1.cases bisim1_list1.cases)
  from exec_1_simulates_Red1_\<tau>[OF wf red[unfolded h1'] bisim \<tau>] obtain xcp' frs'
    where exec: "(if sim12_size e' < sim12_size e then \<tau>Exec_1_dr else \<tau>Exec_1_dt) (compP2 P) (xcp, h, frs) (xcp', h, frs')"
    and bisim': "bisim1_list1 P h (e', xs') exs' xcp' frs'" by blast
  from exec have "(if (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e') (((e', xs'), exs'), h) (((e, xs), exs), h) then \<tau>trsys.silent_moves (mexecd (compP2 P)) (\<tau>MOVE2 (compP2 P)) else \<tau>trsys.silent_movet (mexecd (compP2 P)) (\<tau>MOVE2 (compP2 P))) ((xcp, frs), h) ((xcp', frs'), h)"
    by(auto simp add: \<tau>Exec_1_dr_conv_rtranclp \<tau>Exec_1_dt_conv_tranclp)
  thus "wbisim1 P s1' s2 \<and> (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e')\<^sup>+\<^sup>+ s1' s1 \<or>
       (\<exists>s2'. (\<tau>trsys.silent_move (mexecd (compP2 P)) (\<tau>MOVE2 (compP2 P)))\<^sup>+\<^sup>+ s2 s2' \<and> wbisim1 P s1' s2')"
    using bisim' s1 s1' s2
    by -(rule delay_bisimulation_base.simulation_silent1I', auto split del: split_if)
next
  fix s1 s2 s2'
  assume "wbisim1 P s1 s2" and "\<tau>trsys.silent_move (mexecd (compP2 P)) (\<tau>MOVE2 (compP2 P)) s2 s2'"
  moreover obtain e xs exs h1 where s1: "s1 = (((e, xs), exs), h1)" by(cases s1) auto
  moreover obtain xcp frs h where s2: "s2 = ((xcp, frs), h)" by(cases s2) auto
  moreover obtain xcp' frs' h2' where s2': "s2' = ((xcp', frs'), h2')" by(cases s2') auto
  ultimately have [simp]: "h1 = h" and exec: "exec_1_d (compP2 P) (Normal (xcp, h, frs)) \<epsilon> (Normal (xcp', h2', frs'))"
    and \<tau>: "\<tau>Move2 (compP2 P) (xcp, h, frs)" and bisim: "bisim1_list1 P h (e, xs) exs xcp frs" by(auto)
  from \<tau>Red1_simulates_exec_1_\<tau>[OF wf exec bisim \<tau>]
  obtain e' xs' exs' where [simp]: "h2' = h"
    and red: "(if sim21_size (compP2 P) (xcp', frs') (xcp, frs) then \<tau>Red1r else \<tau>Red1t) P h ((e, xs), exs) ((e', xs'), exs')"
    and bisim': "bisim1_list1 P h (e', xs') exs' xcp' frs'" by blast
  from red have "(if ((\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs') ((xcp', frs'), h2') ((xcp, frs), h)) then \<tau>trsys.silent_moves (mred1 P) (\<tau>MOVE1 P) else \<tau>trsys.silent_movet (mred1 P) (\<tau>MOVE1 P)) (((e, xs), exs), h) (((e', xs'), exs'), h)"
    by(auto dest: \<tau>Red1r_rtranclpD \<tau>Red1t_tranclpD)
  thus "wbisim1 P s1 s2' \<and> (\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs')\<^sup>+\<^sup>+ s2' s2 \<or>
       (\<exists>s1'. (\<tau>trsys.silent_move (mred1 P) (\<tau>MOVE1 P))\<^sup>+\<^sup>+ s1 s1' \<and> wbisim1 P s1' s2')"
    using bisim' s1 s2 s2'
    by -(rule delay_bisimulation_base.simulation_silent2I', auto split del: split_if)
next
  fix s1 s2 tl1 s1'
  assume "wbisim1 P s1 s2" and "mred1 P s1 tl1 s1'" and "\<not> \<tau>MOVE1 P s1 tl1 s1'"
  moreover obtain e xs exs h where s1: "s1 = (((e, xs), exs), h)" by(cases s1) auto
  moreover obtain e' xs' exs' h1' where s1': "s1' = (((e', xs'), exs'), h1')" by(cases s1') auto
  moreover obtain xcp frs h2 where s2: "s2 = ((xcp, frs), h2)" by(cases s2) auto
  ultimately have [simp]: "h2 = h"  and red: "P \<turnstile>1 \<langle>(e, xs)/exs,h\<rangle> -tl1\<rightarrow> \<langle>(e', xs')/exs',h1'\<rangle>"
    and \<tau>: "\<not> \<tau>Move1 P h ((e, xs), exs)" and bisim: "bisim1_list1 P h (e, xs) exs xcp frs"
    by(fastsimp elim!: Red1.cases dest: red1_\<tau>_taD)+
  from exec_1_simulates_Red1_not_\<tau>[OF wf red bisim \<tau>] obtain ta' xcp' frs' xcp'' frs''
    where exec1: "\<tau>Exec_1_dr (compP2 P) (xcp, h, frs) (xcp', h, frs')"
    and exec2: "exec_1_d (compP2 P) (Normal (xcp', h, frs')) ta' (Normal (xcp'', h1', frs''))"
    and \<tau>': "\<not> \<tau>Move2 (compP2 P) (xcp', h, frs')"
    and bisim': "bisim1_list1 P h1' (e', xs') exs' xcp'' frs''"
    and ta': "ta_bisim (wbisim1 P) tl1 ta'" by blast
  from exec1 have "\<tau>trsys.silent_moves (mexecd (compP2 P)) (\<tau>MOVE2 (compP2 P)) ((xcp, frs), h) ((xcp', frs'), h)"
    by(rule \<tau>Exec_1_dr_rtranclpD)
  thus "\<exists>s2' s2'' tl2. \<tau>trsys.silent_moves (mexecd (compP2 P)) (\<tau>MOVE2 (compP2 P)) s2 s2' \<and> 
                       mexecd (compP2 P) s2' tl2 s2'' \<and> \<not> \<tau>MOVE2 (compP2 P) s2' tl2 s2'' \<and>
                       wbisim1 P s1' s2'' \<and> ta_bisim (wbisim1 P) tl1 tl2"
    using bisim' exec2 \<tau>' s1 s1' s2 ta' unfolding `h2 = h`
    apply(subst (1 2) split_paired_Ex)
    apply(subst (1 2) split_paired_Ex)
    by clarify ((rule exI conjI|assumption)+, auto)
next
  fix s1 s2 tl2 s2'
  assume "wbisim1 P s1 s2" and "mexecd (compP2 P) s2 tl2 s2'" and "\<not> \<tau>MOVE2 (compP2 P) s2 tl2 s2'"
  moreover obtain e xs exs h1 where s1: "s1 = (((e, xs), exs), h1)" by(cases s1) auto
  moreover obtain xcp frs h where s2: "s2 = ((xcp, frs), h)" by(cases s2) auto
  moreover obtain xcp' frs' h2' where s2': "s2' = ((xcp', frs'), h2')" by(cases s2') auto
  ultimately have [simp]: "h1 = h"  and exec: "exec_1_d (compP2 P) (Normal (xcp, h, frs)) tl2 (Normal (xcp', h2', frs'))"
    and \<tau>: "\<not> \<tau>Move2 (compP2 P) (xcp, h, frs)" and bisim: "bisim1_list1 P h (e, xs) exs xcp frs"
    apply auto
    apply(erule jvmd_NormalE)
    apply(cases xcp)
    apply auto
    apply(rename_tac stk loc C M pc frs)
    apply(case_tac "instrs_of (compP2 P) C M ! pc")
    apply(simp_all split: split_if_asm)
    done
  from \<tau>Red1_simulates_exec_1_not_\<tau>[OF wf exec bisim \<tau>] obtain e' xs' exs' ta' e'' xs'' exs''
    where red1: "\<tau>Red1r P h ((e, xs), exs) ((e', xs'), exs')"
    and red2: "P \<turnstile>1 \<langle>(e', xs')/exs',h\<rangle> -ta'\<rightarrow> \<langle>(e'', xs'')/exs'',h2'\<rangle>"
    and \<tau>': "\<not> \<tau>Move1 P h ((e', xs'), exs')" and ta': "ta_bisim (wbisim1 P) ta' tl2"
    and bisim': "bisim1_list1 P h2' (e'', xs'') exs'' xcp' frs'" by blast
  from red1 have "\<tau>trsys.silent_moves (mred1 P) (\<tau>MOVE1 P) (((e, xs), exs), h) (((e', xs'), exs'), h)"
    by(rule \<tau>Red1r_rtranclpD)
  thus "\<exists>s1' s1'' tl1. \<tau>trsys.silent_moves (mred1 P) (\<tau>MOVE1 P) s1 s1' \<and> mred1 P s1' tl1 s1'' \<and>
                      \<not> \<tau>MOVE1 P s1' tl1 s1'' \<and> wbisim1 P s1'' s2' \<and> ta_bisim (wbisim1 P) tl1 tl2"
    using bisim' red2 \<tau>' s1 s2 s2' `h1 = h` ta'
    apply -
    apply(rule exI[where x="(((e', xs'), exs'), h)"])
    apply(rule exI[where x="(((e'', xs''), exs''), h2')"])
    apply(rule exI[where x="ta'"])
    apply auto
    done
next
  have "wf (inv_image {(x, y). x < y} (\<lambda>(((e, xs), exs), h). sim12_size e))"
    by(rule wf_inv_image)(rule wf_less)
  also have "inv_image {(x, y). x < y} (\<lambda>(((e, xs), exs), h). sim12_size e) =
    {(x, y). (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e') x y}" by auto
  finally show "wfP (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e')"
    unfolding wfP_def .
next
  from wfP_sim21_size
  have "wf {(xcpfrs, xcpfrs'). sim21_size (compP2 P) xcpfrs xcpfrs'}" by(unfold wfP_def)
  hence "wf (inv_image {(xcpfrs, xcpfrs'). sim21_size (compP2 P) xcpfrs xcpfrs'} fst)" by(rule wf_inv_image)
  also have "inv_image {(xcpfrs, xcpfrs'). sim21_size (compP2 P) xcpfrs xcpfrs'} fst =
    {((xcpfrs, h), (xcpfrs', h)). sim21_size (compP2 P) xcpfrs xcpfrs'}" by auto
  finally show "wfP (\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs')"
    unfolding wfP_def by(auto simp add: split_def)
qed

lemma Red1_final_wf: "final_thread_wf final_expr1 (mred1 P)"
by(unfold_locales)(auto elim!: Red1.cases final.cases)

interpretation Red1_final_wf: final_thread_wf final_expr1 "mred1 P" for P
by(rule Red1_final_wf)

lemma mexecd_final_wf: "final_thread_wf JVM_final (mexecd P)"
by(unfold_locales)(auto elim!: jvmd_NormalE)

interpretation mexecd_final_wf: final_thread_wf JVM_final "mexecd P" for P
by(rule mexecd_final_wf)

interpretation Red1_execd_FWbase:
  FWbisimulation_base final_expr1 "mred1 P" JVM_final "mexecd (compP2 P)" "wbisim1 P" for P
.

lemma \<tau>exec_1_heap_unchanged:
  assumes exec: "exec_1_d (compP2 P) (Normal (xcp, h, frs)) \<epsilon> (Normal (xcp', h', frs'))"
  and bl: "bisim1_list1 P h ex exs xcp frs"
  and \<tau>: "\<tau>Move2 (compP2 P) (xcp, h, frs)"
  shows "h' = h"
using bl exec \<tau>
apply(cases)
apply(auto elim!: jvmd_NormalE)
apply(cases xcp)
apply auto
apply(rename_tac stk loc C M pc FRS)
apply(case_tac "instrs_of (compP2 P) C M ! pc")
apply(simp_all split: split_if_asm)
done

interpretation mexecd_\<tau>mthr: \<tau>multithreaded JVM_final "mexecd P" "\<tau>MOVE2 P" for P
by(unfold_locales)

interpretation Red1_\<tau>mthr: \<tau>multithreaded final_expr1 "mred1 P" "\<tau>MOVE1 P" for P
by(unfold_locales)

interpretation Red1_execd_FWwbase:
  FWdelay_bisimulation_base final_expr1 "mred1 P" JVM_final "mexecd (compP2 P)" "wbisim1 P" "\<tau>MOVE1 P" "\<tau>MOVE2 (compP2 P)" for P
by(unfold_locales)

interpretation Red1_\<tau>mthr_wf:
  \<tau>multithreaded_wf final_expr1 "mred1 P" "\<tau>MOVE1 P" wfs for wfs P
by(rule Red1_\<tau>mthr_wf)

lemma mexecd_\<tau>mthr_wf: "\<tau>multithreaded_wf JVM_final (mexecd (compP2 P)) (\<tau>MOVE2 (compP2 P)) (\<lambda>s2. \<exists>s1. wbisim1 P s1 s2)"
proof
  fix x2 m2 ta2 x2' m2'
  assume "\<exists>s1. wbisim1 P s1 (x2, m2)" "mexecd (compP2 P) (x2, m2) ta2 (x2', m2')"
    and "\<tau>MOVE2 (compP2 P) (x2, m2) ta2 (x2', m2')"
  thus "m2 = m2'" by(cases x2, cases x2')(auto dest: \<tau>exec_1_heap_unchanged)
qed simp

interpretation mexecd_\<tau>mthr_wf:
  \<tau>multithreaded_wf JVM_final "mexecd (compP2 P)" "\<tau>MOVE2 (compP2 P)" "\<lambda>s2. \<exists>s1. wbisim1 P s1 s2" for P
by(rule mexecd_\<tau>mthr_wf)

lemma wbisim1_final_eq:
  "wbisim1 P (exs, h) (\<sigma>, h') \<Longrightarrow> final_expr1 exs \<longleftrightarrow> JVM_final \<sigma>"
apply(cases exs, cases \<sigma>)
apply(auto elim: bisim1_list1.cases)
done

theorem Red1_exec1_FWwbisim:
  assumes wf: "wf_J1_prog P"
  shows "FWdelay_bisimulation_measure final_expr1 (mred1 P) JVM_final (mexecd (compP2 P)) (wbisim1 P) (\<tau>MOVE1 P) (\<tau>MOVE2 (compP2 P)) (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e') (\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs')"
proof -
  let ?exec = "mexecd (compP2 P)"
  let ?\<tau>exec = "\<tau>trsys.silent_moves (mexecd (compP2 P)) (\<tau>MOVE2 (compP2 P))"
  let ?\<tau>red = "\<tau>trsys.silent_moves (mred1 P) (\<tau>MOVE1 P)"
  interpret delay_bisimulation_measure "mred1 P" ?exec "wbisim1 P" "ta_bisim (wbisim1 P)" "\<tau>MOVE1 P" "\<tau>MOVE2 (compP2 P)" "\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e'" "\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs'"
    by(intro Red1_execd_weak_bisim wf)
  show ?thesis
  proof
    fix s1 s2
    assume "wbisim1 P s1 s2" "(\<lambda>(x1, m). final_expr1 x1) s1"
    moreover hence "(\<lambda>(x2, m). JVM_final x2) s2" by(cases s1)(cases s2,auto dest: wbisim1_final_eq)
    ultimately show "\<exists>s2'. ?\<tau>exec s2 s2' \<and> wbisim1 P s1 s2' \<and> (\<lambda>(x2, m). JVM_final x2) s2'" by fastsimp
  next
    fix s1 s2
    assume "wbisim1 P s1 s2" "(\<lambda>(x2, m). JVM_final x2) s2"
    moreover hence "(\<lambda>(x1, m). final_expr1 x1) s1" by(cases s1)(cases s2,auto dest: wbisim1_final_eq)
    ultimately show "\<exists>s1'. ?\<tau>red s1 s1' \<and> wbisim1 P s1' s2 \<and> (\<lambda>(x1, m). final_expr1 x1) s1'" by fastsimp
  next
    fix x m1 xx m2 x1 x2 x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume b: "wbisim1 P (x, m1) (xx, m2)" and b': "wbisim1 P (x1, m1) (x2, m2)"
      and "?\<tau>red (x1, m1) (x1', m1)"
      and red: "mred1 P (x1', m1) ta1 (x1'', m1')"
      and "\<not> \<tau>MOVE1 P (x1', m1) ta1 (x1'', m1')"
      and \<tau>exec: "?\<tau>exec (x2, m2) (x2', m2)"
      and exec: "?exec (x2', m2) ta2 (x2'', m2')"
      and "\<not> \<tau>MOVE2 (compP2 P) (x2', m2) ta2 (x2'', m2')"
      and b2: "wbisim1 P (x1'', m1') (x2'', m2')"
    from red have "hext m1 m1'" by(auto simp add: split_beta intro: Red1_hext_incr)
    moreover from b2 have "m1' = m2'" by(cases x1'', cases x2'') simp
    moreover from b2 have "P \<turnstile> m2' \<surd>"
      by(cases x1'', cases x2'')(auto elim!: bisim1_list1.cases simp add: correct_state_def compP2_def)
    moreover from b have "preallocated m2"
      by(cases x, cases xx)(auto elim!: bisim1_list1.cases simp add: hconf_def correct_state_def compP2_def)
    moreover from \<tau>exec have \<tau>exec': "\<tau>Exec_1_dr (compP2 P) (fst x2, m2, snd x2) (fst x2', m2, snd x2')"
      unfolding \<tau>Exec_1_dr_conv_rtranclp by(simp add: split_def)
    with b' have "compP2 P,compTP P \<turnstile> (fst x2', m2, snd x2') \<surd>"
      apply(cases x1, cases x2)
      apply(erule \<tau>Exec_1_dr_preserves_correct_state[OF wt_compTP_compP2[OF wf]])
      apply(auto elim!: bisim1_list1.cases simp add: correct_state_def)
      done
    ultimately show "wbisim1 P (x, m1') (xx, m2')" using b exec
      apply(cases x, cases xx)
      apply(auto elim!: bisim1_list1.cases intro!: bisim1_list1.intros)
        apply(erule (2) correct_state_heap_change[OF wt_compTP_compP2[OF wf]])
       apply(erule (1) bisim1_hext_mono)
      apply(erule list_all2_mono)
      apply(erule (1) bisim1_fr_hext_mono)
      done
  qed
qed

end