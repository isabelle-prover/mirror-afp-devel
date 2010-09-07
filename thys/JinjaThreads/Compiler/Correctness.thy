(*  Title:      JinjaThreads/Compiler/Correctness.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of both stages} *}

theory Correctness 
imports
  J0Bisim
  J1Deadlock 
  "../Framework/FWBisimDeadlock"
  Correctness2Threaded 
  Correctness1Threaded
  Correctness1
  JJ1WellForm
begin

locale J_JVM_heap_conf_base = 
  J0_J1_heap_base       empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write +
  J1_JVM_heap_conf_base empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf "compP1 P"
  for empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "J_prog"
begin

definition bisimJ2JVM :: "((addr,addr,expr\<times>locals,'heap,addr) state, (addr,addr,addr option \<times> frame list,'heap,addr) state) bisim"
where "bisimJ2JVM = red_red0.mbisim \<circ>\<^isub>B red0_Red1'.mbisim \<circ>\<^isub>B mbisim_Red1'_Red1 \<circ>\<^isub>B Red1_execd.mbisim"

definition tlsimJ2JVM :: "(thread_id \<times> (expr\<times>locals,'heap) JT_thread_action,
                        thread_id \<times> (addr option \<times> frame list,'heap) JT_thread_action) bisim"
where "tlsimJ2JVM = red_red0.mta_bisim \<circ>\<^isub>B red0_Red1'.mta_bisim \<circ>\<^isub>B op = \<circ>\<^isub>B Red1_execd.mta_bisim"

end

definition J2JVM :: "J_prog \<Rightarrow> jvm_prog"
where "J2JVM \<equiv> compP2 \<circ> compP1"

lemma compP2_has_method [simp]: "compP2 P \<turnstile> C has M \<longleftrightarrow> P \<turnstile> C has M" -- "Move to PCompiler"
by(auto simp add: compP2_def compP_has_method)


locale J_JVM_conf_read = 
  J1_JVM_conf_read empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf "compP1 P"
  for empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "J_prog"

sublocale J_JVM_conf_read < J_JVM_heap_conf_base
by(unfold_locales)

sublocale J_JVM_conf_read < J_heap_base .

context J_JVM_conf_read begin

theorem bisimJ2JVM_weak_bisim:
  assumes wf: "wf_J_prog P"
  shows "delay_bisimulation_diverge_final (mredT P) (execd_mthr.redT (J2JVM P)) bisimJ2JVM tlsimJ2JVM 
                                    (red_red0.m\<tau>move1 P) Red1_execd.m\<tau>move2 red_mthr.mfinal exec_mthr.mfinal"
proof -
  interpret b0: FWdelay_bisimulation_measure final_expr "mred P" final_expr0 "mred0 P" "\<lambda>t. bisim_red_red0" "\<lambda>exs (e0, es0). is_call e0" "\<tau>MOVE P" "\<tau>MOVE0 P" "\<lambda>e e'. False" "\<lambda>((e, es), h) ((e, es'), h). length es < length es'"
    by(rule red_red0_FWbisim[OF wf_prog_wwf_prog[OF wf]])
  interpret b01: FWdelay_bisimulation_measure final_expr0 "mred0 P" final_expr1 "mred1' (compP1 P)" "\<lambda>t. bisim_red0_Red1" "bisim_wait01" "\<tau>MOVE0 P" "\<tau>MOVE1 (compP1 P)" "\<lambda>es es'. False" "\<lambda>(((e', xs'), exs'), h') (((e, xs), exs), h). countInitBlock e'< countInitBlock e"
    by(rule red0_Red1'_FWweak_bisim[OF wf])
  interpret b11: bisimulation_into_delay "Red1'_mthr.redT (compP1 P)" "Red1_mthr.redT (compP1 P)" "mbisim_Red1'_Red1" "op =" "Red1'_mthr.m\<tau>move (compP1 P)" "Red1_mthr.m\<tau>move (compP1 P)"
    using compP1_pres_wf[OF wf] by(rule Red1'_Red1_bisim_into_weak)
  interpret b11': bisimulation_final "Red1'_mthr.redT (compP1 P)" "Red1_mthr.redT (compP1 P)" "mbisim_Red1'_Red1" "op =" Red1_mthr.mfinal Red1_mthr.mfinal
    by(unfold_locales)(auto simp add: mbisim_Red1'_Red1_def)
  interpret b12: FWdelay_bisimulation_measure final_expr1 "mred1 (compP1 P)" JVM_final "mexecd (compP2 (compP1 P))"
                                   "wbisim1" "bisim_wait1JVM (compP2 (compP1 P))" "\<tau>MOVE1 (compP1 P)" "\<tau>MOVE2 (compP2 (compP1 P))"
                                   "\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e'"
                                   "\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 (compP1 P)) xcpfrs xcpfrs'"
    using compP1_pres_wf[OF wf] by(intro Red1_exec1_FWwbisim)
  show ?thesis unfolding bisimJ2JVM_def tlsimJ2JVM_def J2JVM_def o_def
    apply(rule delay_bisimulation_diverge_final_compose)
     apply(rule b0.mthr.delay_bisimulation_diverge_final_axioms)
    apply(rule delay_bisimulation_diverge_final_compose)
     apply(rule b01.mthr.delay_bisimulation_diverge_final_axioms)
    apply(rule delay_bisimulation_diverge_final_compose)
     apply(rule delay_bisimulation_diverge_final.intro)
      apply(rule b11.delay_bisimulation)
     apply(rule b11'.delay_bisimulation_final_base_axioms)
    apply(rule b12.mthr.delay_bisimulation_diverge_final_axioms)
    done
qed

lemma bisimJ2JVM_start:
  assumes wf: "wf_J_prog P"
  and start: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=(pns,body) in C"
  and vs: "length vs = length pns" and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  shows "bisimJ2JVM (J_start_state P C M vs) (JVM_start_state (J2JVM P) C M vs)"
using assms sees_method_compP[OF sees, of "\<lambda>C M Ts T (pns, body). compE1 (this # pns) body"]
unfolding bisimJ2JVM_def J2JVM_def o_def
apply(intro bisim_composeI)
   apply(erule (3) bisim_J_J0_start)
  apply(erule (3) bisim_J0_J1_start)
 apply(erule bisim_J1_J1_start[OF compP1_pres_wf])
  apply simp
 apply(simp add: heap_base.compP_confs)
apply(rule bisim_J1_JVM_start[OF compP1_pres_wf])
apply(simp_all add: heap_base.compP_confs)
done

end

fun exception :: "expr \<times> locals \<Rightarrow> addr option \<times> frame list"
where "exception (Throw a, xs) = (\<lfloor>a\<rfloor>, [])"
| "exception _ = (None, [])"

definition mexception :: "(addr,addr,expr\<times>locals,'heap,addr) state \<Rightarrow> (addr,addr,addr option\<times>frame list,'heap,addr) state"
where "mexception s \<equiv> (locks s, (\<lambda>t. case thr s t of \<lfloor>(e, ln)\<rfloor> \<Rightarrow> \<lfloor>(exception e, ln)\<rfloor> | None \<Rightarrow> None, shr s), wset s)"

declare compP1_def [simp del]

context J_JVM_heap_conf_base begin

lemma bisimJ2JVM_mfinal_mexception:
  assumes bisim: "bisimJ2JVM s s'"
  and fin: "exec_mthr.mfinal s'"
  and fin': "red_mthr.mfinal s"
  and tsNotEmpty: "thr s t \<noteq> None"
  shows "s' = mexception s"
proof -
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s) auto
  from bisim obtain s0 s1 where bisimJ0: "red_red0.mbisim s s0"
    and bisim01: "red0_Red1'.mbisim s0 s1"
    and bisim1JVM: "Red1_execd.mbisim s1 s'"
    unfolding bisimJ2JVM_def by(fastsimp simp add: mbisim_Red1'_Red1_def)
  from bisimJ0 s have [simp]: "locks s0 = ls" "wset s0 = ws"
    and tbisimJ0: "\<And>t. red_red0.tbisim (ws t = None) t (ts t) m (thr s0 t) (shr s0)"
    by(auto simp add: red_red0.mbisim_def)
  from bisim01 have [simp]: "locks s1 = ls" "wset s1 = ws"
    and tbisim01: "\<And>t. red0_Red1'.tbisim (ws t = None) t (thr s0 t) (shr s0) (thr s1 t) (shr s1)"
    by(auto simp add: red0_Red1'.mbisim_def)
  from bisim1JVM have "locks s' = ls" "wset s' = ws"
    and tbisim1JVM: "\<And>t. Red1_execd.tbisim (ws t = None) t (thr s1 t) (shr s1) (thr s' t) (shr s')"
    by(auto simp add: Red1_execd.mbisim_def)
  then obtain ts' m' where s': "s' = (ls, (ts', m'), ws)" by(cases s') fastsimp
  { fix t e x ln
    assume tst: "ts t = \<lfloor>((e, x), ln)\<rfloor>"
    from tbisimJ0[of t] tst obtain e' exs' where ts0t: "thr s0 t = \<lfloor>((e', exs'), ln)\<rfloor>"
      and bisimtJ0: "bisim_red_red0 ((e, x), m) ((e', exs'), shr s0)"
      by(auto simp add: red_red0.tbisim_def)
    from tbisim01[of t] ts0t obtain e'' xs'' exs''
      where ts1t: "thr s1 t = \<lfloor>(((e'', xs''), exs''), ln)\<rfloor>"
      and bisimt01: "bisim_red0_Red1 ((e', exs'), shr s0) (((e'', xs''), exs''), shr s1)"
      by(auto simp add: red0_Red1'.tbisim_def)
    from tbisim1JVM[of t] ts1t s' obtain xcp frs
      where ts't: "ts' t = \<lfloor>((xcp, frs), ln)\<rfloor>" and [simp]: "m' = shr s1"
      and bisimt1JVM: "bisim1_list1 t m' (e'', xs'') exs'' xcp frs"
      by(fastsimp simp add: Red1_execd.tbisim_def)

    from fin ts't s s' have [simp]: "frs = []" by(auto dest: exec_mthr.mfinalD)
    from bisimt1JVM have [simp]: "exs'' = []" by(auto elim: bisim1_list1.cases)
    from bisimt01 have [simp]: "exs' = []"
      by(auto simp add: bisim_red0_Red1_def elim!: bisim_list1E elim: bisim_list.cases)
    from tst fin' s have fine: "final e" by(auto dest: red_mthr.mfinalD)
    hence "exception (e, x) = (xcp, frs)"
    proof(cases)
      fix v
      assume [simp]: "e = Val v"
      from bisimtJ0 have "e' = Val v" by(auto elim!: bisim_red_red0.cases)
      with bisimt01 have "e'' = Val v" by(auto simp add: bisim_red0_Red1_def elim: bisim_list1E)
      with bisimt1JVM have "xcp = None" by(auto elim: bisim1_list1.cases)
      thus ?thesis by simp
    next
      fix a
      assume [simp]: "e = Throw a"
      from bisimtJ0 have "e' = Throw a" by(auto elim!: bisim_red_red0.cases)
      with bisimt01 have "e'' = Throw a" by(auto simp add: bisim_red0_Red1_def elim: bisim_list1E)
      with bisimt1JVM have "xcp = \<lfloor>a\<rfloor>" by(auto elim: bisim1_list1.cases)
      thus ?thesis by simp
    qed
    moreover from bisimtJ0 have "shr s0 = m" by(auto elim: bisim_red_red0.cases)
    moreover from bisimt01 have "shr s1 = shr s0" by(auto simp add: bisim_red0_Red1_def)
    ultimately have "ts' t = \<lfloor>(exception (e, x), ln)\<rfloor>" "m' = m" using ts't by simp_all }
  moreover {
    fix t
    assume "ts t = None"
    with red_red0.mbisim_thrNone_eq[OF bisimJ0, of t] s have "thr s0 t = None" by simp
    with bisim01 have "thr s1 t = None" by(auto simp add: red0_Red1'.mbisim_thrNone_eq)
    with bisim1JVM s' have "ts' t = None" by(simp add: Red1_execd.mbisim_thrNone_eq) }
  ultimately show ?thesis using s s' tsNotEmpty by(auto simp add: mexception_def ext_iff)
qed

end


context J_JVM_conf_read begin

theorem J2JVM_correct:
  fixes C M vs
  defines s: "s \<equiv> J_start_state P C M vs"
  and comps: "cs \<equiv> JVM_start_state (J2JVM P) C M vs"
  assumes wf: "wf_J_prog P"
  and start: "start_heap_ok"
  and sees': "P \<turnstile> C sees M:Ts\<rightarrow>T=(pns,body) in C"
  and vs: "length vs = length pns" and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" 
  shows
  "\<lbrakk> red_mthr.mthr.\<tau>rtrancl3p P s ttas s'; red_mthr.mfinal s' \<rbrakk>
  \<Longrightarrow> \<exists>ttas'. execd_mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' (mexception s') \<and>
             bisimulation_base.Tlsim tlsimJ2JVM ttas ttas'" (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?thesis1")
  and
  "\<lbrakk> execd_mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'; exec_mthr.mfinal cs' \<rbrakk>
  \<Longrightarrow> \<exists>s' ttas. red_mthr.mthr.\<tau>rtrancl3p P s ttas s' \<and> mexception s' = cs' \<and>
               bisimulation_base.Tlsim tlsimJ2JVM ttas ttas'" (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?thesis2")
  and
  "red_mthr.mthr.\<tau>inf_step P s Ttas
  \<Longrightarrow> \<exists>Ttas'. execd_mthr.mthr.\<tau>inf_step (J2JVM P) cs Ttas' \<and> bisimulation_base.Tlsiml tlsimJ2JVM Ttas Ttas'"
  (is "_ \<Longrightarrow> ?thesis3")
  and
  "execd_mthr.mthr.\<tau>inf_step (J2JVM P) cs Ttas'
  \<Longrightarrow> \<exists>Ttas. red_mthr.mthr.\<tau>inf_step P s Ttas \<and> bisimulation_base.Tlsiml tlsimJ2JVM Ttas Ttas'"
  (is "_ \<Longrightarrow> ?thesis4")
  and
  "\<lbrakk> red_mthr.mthr.\<tau>rtrancl3p P s ttas s'; red_mthr.deadlock P s' \<rbrakk>
  \<Longrightarrow> \<exists>cs' ttas'. execd_mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs' \<and>
                 execd_mthr.deadlock (J2JVM P) cs' \<and> bisimJ2JVM s' cs' \<and>
                 bisimulation_base.Tlsim tlsimJ2JVM ttas ttas'" (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?thesis5")
  and
  "\<lbrakk> execd_mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'; execd_mthr.deadlock (J2JVM P) cs' \<rbrakk>
  \<Longrightarrow> \<exists>s' ttas. red_mthr.mthr.\<tau>rtrancl3p P s ttas s' \<and> red_mthr.deadlock P s' \<and> bisimJ2JVM s' cs' \<and>
               bisimulation_base.Tlsim tlsimJ2JVM ttas ttas'" (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?thesis6")
proof -
  interpret delay_bisimulation_diverge_final "mredT P" "execd_mthr.redT (J2JVM P)" "bisimJ2JVM" "tlsimJ2JVM" "red_red0.m\<tau>move1 P" "Red1_execd.m\<tau>move2" red_mthr.mfinal exec_mthr.mfinal
    using wf by(rule bisimJ2JVM_weak_bisim)

  from wf start sees' vs conf have bisim: "bisimJ2JVM s cs" unfolding s comps by(rule bisimJ2JVM_start)
  { assume red: "red_mthr.mthr.\<tau>rtrancl3p P s ttas s'"
    and fin: "red_mthr.mfinal s'"
    
    from final_simulation1[OF bisim red fin] obtain cs' ttas'
      where exec: "execd_mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'"
      and bisim': "bisimJ2JVM s' cs'"
      and fin': "exec_mthr.mfinal cs'" and tlsim: "bisimulation_base.Tlsim tlsimJ2JVM ttas ttas'"
      unfolding J2JVM_def o_def by(clarify)
    moreover from red s have "thr s' start_tid \<noteq> None"
      by -(erule red_mthr.\<tau>rtrancl3p_redT_thread_not_disappear, simp add: start_state_def)
    with bisim' fin' fin have [simp]: "cs' = mexception s'" by(intro bisimJ2JVM_mfinal_mexception disjI1)
    ultimately show ?thesis1 by blast
  next
    assume exec: "execd_mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'"
      and fin: "exec_mthr.mfinal cs'"
    from final_simulation2[OF bisim, folded J2JVM_def[THEN meta_eq_to_obj_eq, unfolded ext_iff, THEN spec, unfolded o_def], OF exec fin]
    obtain s' ttas where red: "red_mthr.mthr.\<tau>rtrancl3p P s ttas s'"
      and bisim': "bisimJ2JVM s' cs'" and fin': "red_mthr.mfinal s'"
      and tlsim: "bisimulation_base.Tlsim tlsimJ2JVM ttas ttas'" by blast
    moreover from red s have "thr s' start_tid \<noteq> None"
      by -(erule red_mthr.\<tau>rtrancl3p_redT_thread_not_disappear, simp add: start_state_def split_beta)
    with bisim' fin fin' have [simp]: "cs' = mexception s'" by(intro bisimJ2JVM_mfinal_mexception disjI2)
    ultimately show ?thesis2 by blast
  next
    assume "red_mthr.mthr.\<tau>inf_step P s Ttas"
    from simulation1_\<tau>inf_step[OF this bisim] show ?thesis3
      unfolding J2JVM_def o_def .
  next
    assume "execd_mthr.mthr.\<tau>inf_step (J2JVM P) cs Ttas'"
    thus ?thesis4 using bisim
      by -(rule simulation2_\<tau>inf_step, auto simp add: J2JVM_def o_def)
  }

next
  interpret b0: FWdelay_bisimulation_measure final_expr "mred P" final_expr0 "mred0 P" "\<lambda>t. bisim_red_red0" "\<lambda>exs (e0, es0). is_call e0" "\<tau>MOVE P" "\<tau>MOVE0 P" "\<lambda>e e'. False" "\<lambda>((e, es), h) ((e, es'), h). length es < length es'"
    by(rule red_red0_FWbisim[OF wf_prog_wwf_prog[OF wf]])
  interpret b01: FWdelay_bisimulation_measure final_expr0 "mred0 P" final_expr1 "mred1' (compP1 P)" "\<lambda>t. bisim_red0_Red1" "bisim_wait01" "\<tau>MOVE0 P" "\<tau>MOVE1 (compP1 P)" "\<lambda>es es'. False" "\<lambda>(((e', xs'), exs'), h') (((e, xs), exs), h). countInitBlock e'< countInitBlock e"
    by(rule red0_Red1'_FWweak_bisim[OF wf])
  interpret b11: bisimulation_into_delay "Red1'_mthr.redT (compP1 P)" "Red1_mthr.redT (compP1 P)" "mbisim_Red1'_Red1" "op =" "Red1'_mthr.m\<tau>move (compP1 P)" "Red1_mthr.m\<tau>move (compP1 P)"
    using compP1_pres_wf[OF wf] by(rule Red1'_Red1_bisim_into_weak)
  interpret b12: FWdelay_bisimulation_measure final_expr1 "mred1 (compP1 P)" JVM_final "mexecd (compP2 (compP1 P))"
                                   "wbisim1" "bisim_wait1JVM (compP2 (compP1 P))" "\<tau>MOVE1 (compP1 P)" "\<tau>MOVE2 (compP2 (compP1 P))"
                                   "\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e'"
                                   "\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 (compP1 P)) xcpfrs xcpfrs'"
    using compP1_pres_wf[OF wf] by(intro Red1_exec1_FWwbisim)

  from wf start sees' vs conf have bisim: "bisimJ2JVM s cs" unfolding s comps by(rule bisimJ2JVM_start)
  from bisim obtain s0 s1 s1' where bisim0: "red_red0.mbisim s s0"
    and bisim01: "red0_Red1'.mbisim s0 s1"
    and bisim11: "mbisim_Red1'_Red1 s1 s1'"
    and bisim12: "Red1_execd.mbisim s1' cs"
    unfolding bisimJ2JVM_def by auto
  from bisim11 have "s1' = s1" by(simp add: mbisim_Red1'_Red1_def)
  {
    assume red: "red_mthr.mthr.\<tau>rtrancl3p P s ttas s'"
      and dead: "red_mthr.deadlock P s'"
    from b0.mthr.simulation1_\<tau>rtrancl3p[OF red bisim0]
    obtain ttas0 s0' where "red0_mthr.mthr.\<tau>rtrancl3p P s0 ttas0 s0'"
      and "red_red0.mbisim s' s0'"
      and tlsim0: "bisimulation_base.Tlsim red_red0.mta_bisim ttas ttas0" by auto
    from b0.deadlock1_imp_\<tau>s_deadlock2[OF `red_red0.mbisim s' s0'` dead]
    obtain s0'' where "red0_mthr.mthr.silent_moves P s0' s0''"
      and bisim0': "red_red0.mbisim s' s0''"
      and dead0: "red0_mthr.deadlock P s0''" by auto
    from `red0_mthr.mthr.\<tau>rtrancl3p P s0 ttas0 s0'` `red0_mthr.mthr.silent_moves P s0' s0''`
    have "red0_mthr.mthr.\<tau>rtrancl3p P s0 (ttas0 @ []) s0''"
      by(rule red0_mthr.mthr.\<tau>rtrancl3p_trans[OF _ red0_mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    from b01.mthr.simulation1_\<tau>rtrancl3p[OF this bisim01]
    obtain ttas1 s1'' where "Red1'_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 ttas1 s1''"
      and "red0_Red1'.mbisim s0'' s1''"
      and tlsim01: "bisimulation_base.Tlsim red0_Red1'.mta_bisim ttas0 ttas1" by auto
    from b01.deadlock1_imp_\<tau>s_deadlock2[OF `red0_Red1'.mbisim s0'' s1''` dead0]
    obtain s1''' where "Red1'_mthr.mthr.silent_moves (compP1 P) s1'' s1'''"
      and dead1: "Red1'_mthr.deadlock (compP1 P) s1'''"
      and bisim01': "red0_Red1'.mbisim s0'' s1'''" by auto
    from `Red1'_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 ttas1 s1''` `Red1'_mthr.mthr.silent_moves (compP1 P) s1'' s1'''`
    have "Red1'_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 (ttas1 @ []) s1'''"
      by(rule Red1'_mthr.mthr.\<tau>rtrancl3p_trans[OF _ Red1'_mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    from b11.simulation1_\<tau>rtrancl3p[OF this bisim11]
    obtain s1'''' where "Red1_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' ttas1 s1''''"
      and bisim11': "mbisim_Red1'_Red1 s1''' s1''''" by auto
    from b12.mthr.simulation1_\<tau>rtrancl3p[OF `Red1_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' ttas1 s1''''` bisim12]
    obtain ttas' cs' where "execd_mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs ttas' cs'"
      and "Red1_execd.mbisim s1'''' cs'"
      and tlsim12: "list_all2 Red1_execd.mta_bisim ttas1 ttas'" by(auto)
    from bisim11' have "s1''' = s1''''" by(simp add: mbisim_Red1'_Red1_def)
    with dead1 have "Red1_mthr.deadlock (compP1 P) s1''''"
      by(simp add: Red1_Red1'_deadlock_inv)
    from b12.deadlock1_imp_\<tau>s_deadlock2[OF `Red1_execd.mbisim s1'''' cs'` this]
    obtain cs'' where "execd_mthr.mthr.silent_moves (compP2 (compP1 P)) cs' cs''"
      and bisim12': "Red1_execd.mbisim s1'''' cs''"
      and dead': "execd_mthr.deadlock (compP2 (compP1 P)) cs''" by auto
    from `execd_mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs ttas' cs'` `execd_mthr.mthr.silent_moves (compP2 (compP1 P)) cs' cs''`
    have "execd_mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs (ttas' @ []) cs''"
      by(rule execd_mthr.mthr.\<tau>rtrancl3p_trans[OF _ execd_mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    moreover from bisim0' bisim01' bisim11' bisim12' have "bisimJ2JVM s' cs''"
      by(auto simp add: bisimJ2JVM_def J2JVM_def o_def intro: bisim_composeI)
    moreover from tlsim0 tlsim01 tlsim12
    have "list_all2 tlsimJ2JVM ttas ttas'"
      by(auto intro!: list_all2_bisim_composeI simp add: tlsimJ2JVM_def)
    ultimately show ?thesis5 using dead' unfolding J2JVM_def o_def
      by-(rule exI conjI|assumption|simp)+
  next
    assume "execd_mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'"
      and "execd_mthr.deadlock (J2JVM P) cs'"
    hence "execd_mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs ttas' cs'"
      and dead: "execd_mthr.deadlock (compP2 (compP1 P)) cs'"
      by(simp_all add: J2JVM_def o_def)
    from b12.mthr.simulation2_\<tau>rtrancl3p[OF `execd_mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs ttas' cs'` bisim12]
    obtain ttas1 s1'' where "Red1_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' ttas1 s1''"
      and "Red1_execd.mbisim s1'' cs'"
      and tlsim12: "list_all2 Red1_execd.mta_bisim ttas1 ttas'" by(auto)
    from b12.deadlock2_imp_\<tau>s_deadlock1[OF `Red1_execd.mbisim s1'' cs'` dead]
    obtain s1''' where "Red1_mthr.mthr.silent_moves (compP1 P) s1'' s1'''"
      and dead1: "Red1_mthr.deadlock (compP1 P) s1'''"
      and bisim12': "Red1_execd.mbisim s1''' cs'" by auto
    from `Red1_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' ttas1 s1''` `Red1_mthr.mthr.silent_moves (compP1 P) s1'' s1'''`
    have "Red1_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' (ttas1 @ []) s1'''"
      by(rule Red1_mthr.mthr.\<tau>rtrancl3p_trans[OF _ Red1_mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    from b11.simulation2_\<tau>rtrancl3p[OF this bisim11]
    obtain s1'''' where "Red1'_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 ttas1 s1''''"
      and bisim11': "mbisim_Red1'_Red1 s1'''' s1'''" by(auto)
    from b01.mthr.simulation2_\<tau>rtrancl3p[OF `Red1'_mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 ttas1 s1''''` bisim01]
    obtain ttas0 s0' where "red0_mthr.mthr.\<tau>rtrancl3p P s0 ttas0 s0'"
      and "red0_Red1'.mbisim s0' s1''''"
      and tlsim01: "bisimulation_base.Tlsim red0_Red1'.mta_bisim ttas0 ttas1" by auto
    from bisim11' have "s1''' = s1''''" by(simp add: mbisim_Red1'_Red1_def)
    with dead1 have "Red1'_mthr.deadlock (compP1 P) s1''''"
      by(simp add: Red1_Red1'_deadlock_inv)
    from b01.deadlock2_imp_\<tau>s_deadlock1[OF `red0_Red1'.mbisim s0' s1''''` this]
    obtain s0'' where "red0_mthr.mthr.silent_moves P s0' s0''"
      and bisim01': "red0_Red1'.mbisim s0'' s1''''"
      and dead0: "red0_mthr.deadlock P s0''" by auto
    from `red0_mthr.mthr.\<tau>rtrancl3p P s0 ttas0 s0'` `red0_mthr.mthr.silent_moves P s0' s0''`
    have "red0_mthr.mthr.\<tau>rtrancl3p P s0 (ttas0 @ []) s0''"
      by(rule red0_mthr.mthr.\<tau>rtrancl3p_trans[OF _ red0_mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    from b0.mthr.simulation2_\<tau>rtrancl3p[OF this bisim0]
    obtain ttas s' where "red_mthr.mthr.\<tau>rtrancl3p P s ttas s'"
      and "red_red0.mbisim s' s0''"
      and tlsim0: "bisimulation_base.Tlsim red_red0.mta_bisim ttas ttas0" by auto
    from b0.deadlock2_imp_\<tau>s_deadlock1[OF `red_red0.mbisim s' s0''` dead0]
    obtain s'' where "red_mthr.mthr.silent_moves P s' s''"
      and dead': "red_mthr.deadlock P s''"
      and bisim0': "red_red0.mbisim s'' s0''" by auto
    from `red_mthr.mthr.\<tau>rtrancl3p P s ttas s'` `red_mthr.mthr.silent_moves P s' s''`
    have "red_mthr.mthr.\<tau>rtrancl3p P s (ttas @ []) s''"
      by(rule red_mthr.mthr.\<tau>rtrancl3p_trans[OF _ red_mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    moreover from bisim0' bisim01' bisim11' bisim12' have "bisimJ2JVM s'' cs'"
      by(auto simp add: bisimJ2JVM_def J2JVM_def o_def intro: bisim_composeI)
    moreover from tlsim0 tlsim01 tlsim12
    have "list_all2 tlsimJ2JVM ttas ttas'"
      by(auto intro!: list_all2_bisim_composeI simp add: tlsimJ2JVM_def)
    ultimately show ?thesis6 using dead'
      by-(rule exI conjI|assumption|simp)+
  }
qed

end

declare compP1_def [simp]

lemma wt_J2JVM: "wf_J_prog P \<Longrightarrow> wf_jvm_prog (J2JVM P)"
unfolding J2JVM_def o_def
by(rule wt_compP2)(rule compP1_pres_wf)

end