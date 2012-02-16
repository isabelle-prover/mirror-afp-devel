(*  Title:      JinjaThreads/MM/JMM_Compiler.thy
    Author:     Andreas Lochbihler

    Compiler correctness for the JMM
*)

header {* \isaheader{Compiler correctness for the JMM} *}

theory JMM_Compiler imports
  JMM_J
  JMM_JVM
  "../Compiler/Correctness" 
  "../Framework/FWBisimLift"
begin

lemma action_loc_aux_compP [simp]: "action_loc_aux (compP f P) = action_loc_aux P"
by(auto 4 4 elim!: action_loc_aux_cases)

lemma action_loc_compP: "action_loc (compP f P) = action_loc P"
by simp

lemma is_volatile_compP [simp]: "is_volatile (compP f P) = is_volatile P"
proof(rule ext)
  fix hT
  show "is_volatile (compP f P) hT = is_volatile P hT"
    by(cases hT) simp_all
qed

lemma saction_compP [simp]: "saction (compP f P) = saction P"
by(simp add: saction.simps fun_eq_iff)

lemma sactions_compP [simp]: "sactions (compP f P) = sactions P"
by(rule ext)(simp only: sactions_def, simp)

lemma sync_order_compP [simp]: "sync_order (compP f P) = sync_order P"
by(simp add: sync_order_def fun_eq_iff)

lemma sync_with_compP [simp]: "sync_with (compP f P) = sync_with P"
by(simp add: sync_with_def fun_eq_iff)

lemma po_sw_compP [simp]: "po_sw (compP f P) = po_sw P"
by(simp add: po_sw_def fun_eq_iff)

lemma happens_before_compP: "happens_before (compP f P) = happens_before P"
by simp

lemma addr_loc_default_compP [simp]: "addr_loc_default (compP f P) = addr_loc_default P"
proof(intro ext)
  fix hT al
  show "addr_loc_default (compP f P) hT al = addr_loc_default P hT al"
    by(cases "(P, hT, al)" rule: addr_loc_default.cases) simp_all
qed

lemma value_written_aux_compP [simp]: "value_written_aux (compP f P) = value_written_aux P"
proof(intro ext)
  fix a al
  show "value_written_aux (compP f P) a al = value_written_aux P a al"
    by(cases "(P, a, al)" rule: value_written_aux.cases)(simp_all add: value_written_aux.simps)
qed

lemma value_written_compP [simp]: "value_written (compP f P) = value_written P"
by(simp add: fun_eq_iff value_written.simps)

lemma is_write_seen_compP [simp]: "is_write_seen (compP f P) = is_write_seen P"
by(simp add: fun_eq_iff is_write_seen_def)

lemma is_justified_by_compP [simp]: "is_justified_by (compP f P) = is_justified_by P"
by(simp add: fun_eq_iff is_justified_by.simps)

lemma legal_execution_compP: "legal_execution (compP f P) = legal_execution P"
by(simp add: fun_eq_iff legal_execution_def)

lemma most_recent_write_for_compP [simp]: 
  "most_recent_write_for (compP f P) = most_recent_write_for P"
by(simp add: fun_eq_iff most_recent_write_for.simps)

lemma sequentially_consistent_compP [simp]:
  "sequentially_consistent (compP f P) = sequentially_consistent P"
by(simp add: sequentially_consistent_def split_beta)

lemma conflict_compP [simp]: "conflict (compP f P) = conflict P"
by(simp add: fun_eq_iff conflict_def)

lemma correctly_synchronized_compP [simp]: 
  "correctly_synchronized (compP f P) = correctly_synchronized P"
by(simp add: fun_eq_iff correctly_synchronized_def)


context J_JVM_heap_conf_base begin

definition if_bisimJ2JVM :: 
  "(('addr,'thread_id,status \<times> 'addr expr\<times>'addr locals,'heap,'addr) state, 
    ('addr,'thread_id,status \<times> 'addr option \<times> 'addr frame list,'heap,'addr) state) bisim"
where 
  "if_bisimJ2JVM = 
   FWbisimulation_base.mbisim red_red0.init_fin_bisim red_red0.init_fin_bisim_wait \<circ>\<^isub>B
   FWbisimulation_base.mbisim red0_Red1'.init_fin_bisim red0_Red1'.init_fin_bisim_wait \<circ>\<^isub>B
   if_mbisim_Red1'_Red1 \<circ>\<^isub>B 
   FWbisimulation_base.mbisim Red1_execd.init_fin_bisim Red1_execd.init_fin_bisim_wait"

definition if_tlsimJ2JVM ::
  "('thread_id \<times> ('addr, 'thread_id, status \<times> 'addr expr \<times> 'addr locals,
                  'heap, 'addr, ('addr, 'thread_id) obs_event action) thread_action,
    'thread_id \<times> ('addr, 'thread_id, status \<times> 'addr jvm_thread_state,
                  'heap, 'addr, ('addr, 'thread_id) obs_event action) thread_action) bisim"
where
  "if_tlsimJ2JVM = 
   FWbisimulation_base.mta_bisim red_red0.init_fin_bisim \<circ>\<^isub>B 
   FWbisimulation_base.mta_bisim red0_Red1'.init_fin_bisim \<circ>\<^isub>B op = \<circ>\<^isub>B 
   FWbisimulation_base.mta_bisim Red1_execd.init_fin_bisim"

end

sublocale J_JVM_conf_read < red_mthr!: if_\<tau>multithreaded_wf final_expr "mred P" convert_RA "\<tau>MOVE P"
by(unfold_locales)

sublocale J_JVM_conf_read < execd_mthr!: 
  if_\<tau>multithreaded_wf
    JVM_final
    "mexecd (compP2 (compP1 P))"
    convert_RA 
    "\<tau>MOVE2 (compP2 (compP1 P))"
by(unfold_locales)

context J_JVM_conf_read begin

theorem if_bisimJ2JVM_weak_bisim:
  assumes wf: "wf_J_prog P"
  shows "delay_bisimulation_diverge_final
    (red_mthr.mthr.if.redT P) (execd_mthr.mthr.if.redT (J2JVM P)) if_bisimJ2JVM if_tlsimJ2JVM 
    red_mthr.if.m\<tau>move execd_mthr.if.m\<tau>move red_mthr.mthr.if.mfinal execd_mthr.mthr.if.mfinal"
unfolding if_bisimJ2JVM_def if_tlsimJ2JVM_def J2JVM_def o_apply
apply(rule delay_bisimulation_diverge_final_compose)
 apply(rule FWdelay_bisimulation_diverge.mthr_delay_bisimulation_diverge_final)
 apply(rule FWdelay_bisimulation_diverge.init_fin_FWdelay_bisimulation_diverge)
 apply(rule red_red0_FWbisim[OF wf_prog_wwf_prog[OF wf]])
apply(rule delay_bisimulation_diverge_final_compose)
 apply(rule FWdelay_bisimulation_diverge.mthr_delay_bisimulation_diverge_final)
 apply(rule FWdelay_bisimulation_diverge.init_fin_FWdelay_bisimulation_diverge)
 apply(rule red0_Red1'_FWweak_bisim[OF wf])
apply(rule delay_bisimulation_diverge_final_compose)
 apply(rule delay_bisimulation_diverge_final.intro)
  apply(rule bisimulation_into_delay.delay_bisimulation)
  apply(rule if_Red1'_Red1_bisim_into_weak[OF compP1_pres_wf[OF wf]])
 apply(rule bisimulation_final.delay_bisimulation_final_base)
 apply(rule if_Red1'_Red1_bisimulation_final[OF compP1_pres_wf[OF wf]])
apply(rule FWdelay_bisimulation_diverge.mthr_delay_bisimulation_diverge_final)
apply(rule FWdelay_bisimulation_diverge.init_fin_FWdelay_bisimulation_diverge)
apply(rule Red1_exec1_FWwbisim[OF compP1_pres_wf[OF wf]])
done

lemma if_bisimJ2JVM_start:
  assumes wf: "wf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  shows "if_bisimJ2JVM (init_fin_lift_state Running (J_start_state P C M vs))
                       (init_fin_lift_state Running (JVM_start_state (J2JVM P) C M vs))"
using assms
unfolding if_bisimJ2JVM_def J2JVM_def o_apply
apply(intro bisim_composeI)
   apply(rule FWbisimulation_base.init_fin_lift_state_mbisimI)
   apply(erule (1) bisim_J_J0_start[OF wf_prog_wwf_prog])
  apply(rule FWbisimulation_base.init_fin_lift_state_mbisimI)
  apply(erule (1) bisim_J0_J1_start)
 apply(erule if_bisim_J1_J1_start[OF compP1_pres_wf])
 apply simp
apply(rule FWbisimulation_base.init_fin_lift_state_mbisimI)
apply(erule bisim_J1_JVM_start[OF compP1_pres_wf])
apply simp
done

lemma red_Runs_eq_mexecd_Runs:
  fixes C M vs
  defines s: "s \<equiv> init_fin_lift_state Running (J_start_state P C M vs)"
  and comps: "cs \<equiv> init_fin_lift_state Running (JVM_start_state (J2JVM P) C M vs)"
  assumes wf: "wf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  shows "red_mthr.mthr.if.\<E> P s = execd_mthr.mthr.if.\<E> (J2JVM P) cs"
proof -
  from wf wf_start have bisim: "if_bisimJ2JVM s cs"
    unfolding s comps by(rule if_bisimJ2JVM_start)

  interpret divfin!: delay_bisimulation_diverge_final 
    "red_mthr.mthr.if.redT P" 
    "execd_mthr.mthr.if.redT (J2JVM P)"
    "if_bisimJ2JVM"
    "if_tlsimJ2JVM"
    "red_mthr.if.m\<tau>move"
    "execd_mthr.if.m\<tau>move"
    "red_mthr.mthr.if.mfinal"
    "execd_mthr.mthr.if.mfinal"
    using wf by(rule if_bisimJ2JVM_weak_bisim)
  
  show ?thesis (is "?lhs = ?rhs")
  proof(intro equalityI subsetI)
    fix E
    assume "E \<in> ?lhs"
    then obtain E' where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
      and E': "red_mthr.if.mthr.\<tau>Runs s E'"
      unfolding red_mthr.if.\<E>_conv_Runs by blast
    from divfin.simulation_\<tau>Runs1[OF bisim E']
    obtain E'' where E'': "execd_mthr.if.mthr.\<tau>Runs cs E''"
      and tlsim: "tllist_all2 if_tlsimJ2JVM (option_rel if_bisimJ2JVM) E' E''"
      unfolding J2JVM_def o_apply by blast
    let ?E = "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E''))"
    from tlsim have "llist_all2 if_tlsimJ2JVM (llist_of_tllist E') (llist_of_tllist E'')"
      by(rule tllist_all2D_llist_all2_llist_of_tllist)
    hence "llist_all2 (op =) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))
                             (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E''))"
      unfolding llist_all2_lmap1 llist_all2_lmap2
      by(rule llist_all2_mono)(auto simp add: if_tlsimJ2JVM_def FWbisimulation_base.mta_bisim_def ta_bisim_def)
    hence "?E = E" unfolding llist_all2_eq E by simp
    also from E'' have "?E \<in> ?rhs" unfolding J2JVM_def o_apply execd_mthr.if.\<E>_conv_Runs by blast
    finally (subst) show "E \<in> ?rhs" .
  next
    fix E
    assume "E \<in> ?rhs"
    then obtain E' where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
      and E': "execd_mthr.if.mthr.\<tau>Runs cs E'"
      unfolding execd_mthr.if.\<E>_conv_Runs J2JVM_def o_apply by blast
    from divfin.simulation_\<tau>Runs2[OF bisim, unfolded J2JVM_def o_apply, OF E']
    obtain E'' where E'': "red_mthr.if.mthr.\<tau>Runs s E''"
      and tlsim: "tllist_all2 if_tlsimJ2JVM (option_rel if_bisimJ2JVM) E'' E'" by blast
    let ?E = "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E''))"
    from tlsim have "llist_all2 if_tlsimJ2JVM (llist_of_tllist E'') (llist_of_tllist E')"
      by(rule tllist_all2D_llist_all2_llist_of_tllist)
    hence "llist_all2 (op =) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E''))
                             (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
      unfolding llist_all2_lmap1 llist_all2_lmap2
      by(rule llist_all2_mono)(auto simp add: if_tlsimJ2JVM_def FWbisimulation_base.mta_bisim_def ta_bisim_def)
    hence "?E = E" unfolding llist_all2_eq E by simp
    also from E'' have "?E \<in> ?lhs" unfolding red_mthr.if.\<E>_conv_Runs by blast
    finally (subst) show "E \<in> ?lhs" .
  qed
qed

lemma red_\<E>_eq_mexecd_\<E>:
  "\<lbrakk> wf_J_prog P; wf_start_state P C M vs \<rbrakk>
  \<Longrightarrow> J_\<E> P C M vs Running = JVMd_\<E> (J2JVM P) C M vs Running"
by(simp only: red_Runs_eq_mexecd_Runs)

theorem J2JVM_jmm_correct:
  assumes wf: "wf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  shows "legal_execution P (J_\<E> P C M vs Running) (E, ws) \<longleftrightarrow> 
         legal_execution (J2JVM P) (JVMd_\<E> (J2JVM P) C M vs Running) (E, ws)"
by(simp only: red_\<E>_eq_mexecd_\<E>[OF assms] J2JVM_def o_apply compP1_def compP2_def legal_execution_compP)

theorem J2JVM_jmm_correctly_synchronized:
  assumes wf: "wf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  shows "correctly_synchronized (J2JVM P) (JVMd_\<E> (J2JVM P) C M vs Running) \<longleftrightarrow> 
         correctly_synchronized P (J_\<E> P C M vs Running)"
by(simp only: red_\<E>_eq_mexecd_\<E>[OF assms] J2JVM_def o_apply compP1_def compP2_def correctly_synchronized_compP)

end

end
