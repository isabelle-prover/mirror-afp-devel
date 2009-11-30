(*  Title:      JinjaThreads/Compiler/Correctness.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of both stages} *}

theory Correctness 
imports
  Correctness2Threaded
  Correctness1Threaded
  "../Framework/FWBisimDeadlock"
  J1Deadlock
begin

lemma \<tau>moves1_map_Val_ThrowD [simp]: "\<tau>moves1 P h (map Val vs @ Throw a # es) = False" -- "Move to J1"
by(induct vs)(fastsimp)+

lemma assumes nfin: "\<not> final e'" -- "Move to J0"
 shows inline_call_\<tau>move0_inv: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>move0 P h (inline_call e' e) = \<tau>move0 P h e'"
  and inline_calls_\<tau>moves0_inv: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>moves0 P h (inline_calls e' es) = \<tau>move0 P h e'"
apply(induct e and es)
apply(insert nfin)
apply simp_all
apply auto
done

interpretation red_red0_FWbase: FWbisimulation_base final_expr "mred P" final_expr0 "mred0 P" bisim_red_red0 for P
.

definition bisimJ2JVM :: "J_prog \<Rightarrow> ((addr,addr,expr\<times>locals,heap,addr) state,
                                  (addr,addr,addr option \<times> frame list,heap,addr) state) bisim"
where "bisimJ2JVM P = red_red0_FWbase.mbisim \<circ>\<^isub>B red0_Red1_FWbase.mbisim \<circ>\<^isub>B mbisim_Red1'_Red1 \<circ>\<^isub>B (Red1_execd_FWbase.mbisim (compP1 P))"

definition tlsimJ2JVM :: "J_prog \<Rightarrow> (thread_id \<times> (addr,thread_id,expr\<times>locals,heap,addr,(addr,obs_event) observable) thread_action,
                                  thread_id \<times> (addr,thread_id,addr option \<times> frame list,heap,addr,(addr,obs_event) observable) thread_action) bisim"
where "tlsimJ2JVM P = red_red0_FWbase.mta_bisim \<circ>\<^isub>B red0_Red1_FWbase.mta_bisim \<circ>\<^isub>B op = \<circ>\<^isub>B (Red1_execd_FWbase.mta_bisim (compP1 P))"

definition J2JVM :: "J_prog \<Rightarrow> jvm_prog"
where "J2JVM \<equiv> compP2 \<circ> compP1"

lemma compP2_has_method [simp]: "compP2 P \<turnstile> C has M \<longleftrightarrow> P \<turnstile> C has M"
by(auto simp add: compP2_def)

lemma conf_compP [simp]: "compP f P,h \<turnstile> v :\<le> T \<longleftrightarrow> P,h \<turnstile> v :\<le> T"
by(simp add: conf_compP)

declare compP_confs [simp]

interpretation red0_\<tau>mthr_wf: \<tau>multithreaded_wf final_expr0 "mred0 P" "\<tau>MOVE0 P" wfs for P wfs
by(unfold_locales)

interpretation red_red0_FWwbase:
  FWdelay_bisimulation_base final_expr "mred P" final_expr0 "mred0 P" "bisim_red_red0" "\<tau>MOVE P" "\<tau>MOVE0 P" for P
by(unfold_locales)

interpretation Red1_mexecd_FWbase:
  FWbisimulation_base final_expr1 "mred1 P" JVM_final "mexecd (compP2 P)" "wbisim1 P" for P
.

lemma Red1'_Red1_bisim_into_weak:
  assumes wf: "wf_J1_prog P"
  shows "bisimulation_into_delay (Red1'_mthr.redT P) (Red1_mthr.redT P) mbisim_Red1'_Red1 (op =) (Red1'_\<tau>mthr.m\<tau>move P) (Red1_\<tau>mthr.m\<tau>move P)"
proof -
  interpret b: bisimulation "Red1'_mthr.redT P" "Red1_mthr.redT P" "mbisim_Red1'_Red1" "op ="
    by(rule Red1'_Red1_bisimulation[OF wf])
  show ?thesis by(unfold_locales)(simp add: mbisim_Red1'_Red1_def)
qed

interpretation mexecd_\<tau>mthr: \<tau>multithreaded JVM_final "mexecd P" "\<tau>MOVE2 P" for P
by(unfold_locales)

lemmas Red1_mexecd_FWweak_bisim = Red1_exec1_FWwbisim

theorem bisimJ2JVM_weak_bisim:
  assumes wf: "wf_J_prog P"
  shows "delay_bisimulation_diverge_final (mredT P) (execd_mthr.redT (J2JVM P)) (bisimJ2JVM P) (tlsimJ2JVM P) 
                                    (red_red0_FWwbase.m\<tau>move1 P) (Red1_execd_FWwbase.m\<tau>move2 (compP1 P)) red_mthr.mfinal exec_mthr.mfinal"
proof -
  interpret b0: FWdelay_bisimulation_measure final_expr "mred P" final_expr0 "mred0 P" bisim_red_red0 "\<tau>MOVE P" "\<tau>MOVE0 P" "\<lambda>e e'. False" "\<lambda>((e, es), h) ((e, es'), h). length es < length es'"
    by(rule red_red0_FWbisim[OF wf_prog_wwf_prog[OF wf]])
  interpret b01: FWdelay_bisimulation_measure final_expr0 "mred0 P" final_expr1 "mred1' (compP1 P)" bisim_red0_Red1 "\<tau>MOVE0 P" "\<tau>MOVE1 (compP1 P)" "\<lambda>es es'. False" "\<lambda>(((e', xs'), exs'), h') (((e, xs), exs), h). countInitBlock e'< countInitBlock e"
    by(rule red0_Red1'_FWweak_bisim[OF wf])
  interpret b11: bisimulation_into_delay "Red1'_mthr.redT (compP1 P)" "Red1_mthr.redT (compP1 P)" "mbisim_Red1'_Red1" "op =" "Red1'_\<tau>mthr.m\<tau>move (compP1 P)" "Red1_\<tau>mthr.m\<tau>move (compP1 P)"
    using compP1_pres_wf[OF wf] by(rule Red1'_Red1_bisim_into_weak)
  interpret b11': bisimulation_final "Red1'_mthr.redT (compP1 P)" "Red1_mthr.redT (compP1 P)" "mbisim_Red1'_Red1" "op =" Red1'_mthr.mfinal Red1'_mthr.mfinal
    by(unfold_locales)(auto simp add: mbisim_Red1'_Red1_def)
  interpret b12: FWdelay_bisimulation_measure final_expr1 "mred1 (compP1 P)" JVM_final "mexecd (compP2 (compP1 P))"
                                   "wbisim1 (compP1 P)" "\<tau>MOVE1 (compP1 P)" "\<tau>MOVE2 (compP2 (compP1 P))"
                                   "\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e'"
                                   "\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 (compP1 P)) xcpfrs xcpfrs'"
    using compP1_pres_wf[OF wf] by(intro Red1_mexecd_FWweak_bisim)
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
  and sees': "P \<turnstile> D sees M:Ts\<rightarrow>T=(pns,body) in C"
  and vs: "length vs = length pns" and conf: "P,h \<turnstile> vs [:\<le>] Ts" and hconf: "P \<turnstile> h \<surd>"
  and rest: "length rest = max_vars body"
  and ha: "h a = \<lfloor>Obj D fs\<rfloor>"
  shows "bisimJ2JVM P (\<lambda>\<^isup>f None, ([t \<mapsto> ((blocks (this # pns, Class C # Ts, Addr a # vs, body), empty), no_wait_locks)], h), empty)
                      (\<lambda>\<^isup>f None, ([t \<mapsto> ((None, [([], Addr a # vs @ rest, C, M, 0)]), no_wait_locks)], h), empty)"
  (is "bisimJ2JVM _ ?s1 ?s4")
unfolding bisimJ2JVM_def
proof(rule bisim_composeI)
  from sees' have sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=(pns,body) in C" by(rule sees_method_idemp)
  from sees_wf_mdecl[OF wf_prog_wwf_prog[OF wf] sees] have wwfCM: "wwf_J_mdecl P C (M, Ts, T, pns, body)"
    and len: "length pns = length Ts" by(auto simp add: wf_mdecl_def)
  from sees_wf_mdecl[OF wf sees] have wfCM: "wf_J_mdecl P C (M, Ts, T, pns, body)" by(auto simp add: wf_mdecl_def)
  let ?s2 = "(\<lambda>\<^isup>f None, ([t \<mapsto> ((blocks (this # pns, Class C#Ts, Addr a#vs, body), [addr a\<bullet>M(map Val vs)]), no_wait_locks)], h), empty)"
  from wwfCM have fvbody: "fv body \<subseteq> {this} \<union> set pns" and pns: "length pns = length Ts" by simp_all
  with vs len have fv: "fv (blocks (pns, Ts, vs, body)) \<subseteq> {this}" by auto
  from wfCM obtain T' where T'subT: "P \<turnstile> T' \<le> T" and wtbody: "P,[this # pns [\<mapsto>] Class C # Ts] \<turnstile> body :: T'" by auto
  from wtbody have elbody: "expr_locks body = (\<lambda>l. 0)" by(rule WT_expr_locks)
  hence cisbody: "\<not> contains_insync body" by(auto simp add: contains_insync_conv)
  from wfCM len vs have dabody: "\<D> (blocks (pns, Ts, vs, body)) \<lfloor>{this}\<rfloor>" by auto
  from sees have sees1: "compP1 P \<turnstile> C sees M:Ts\<rightarrow>T = compE1 (this # pns) body in C"
    by(auto dest: sees_method_compP[where f="(\<lambda>(pns, body). compE1 (this # pns) body)"])
  from len vs fv ha sees' show "red_red0_FWbase.mbisim ?s1 ?s2"
    by auto(rule red_red0_FWbase.mbisimI,auto intro!: bisim_red_red0.intros simp add: is_call_def split: split_if_asm)
  show "(red0_Red1_FWbase.mbisim \<circ>\<^isub>B mbisim_Red1'_Red1 \<circ>\<^isub>B (Red1_execd_FWbase.mbisim (compP1 P))) ?s2 ?s4"
  proof(rule bisim_composeI)
    let ?e = "blocks1 0 (Class C#Ts) (compE1 (this # pns) body)"
    let ?xs = "Addr a # vs @ rest"
    let ?s3 = "(\<lambda>\<^isup>f None, ([t \<mapsto> (((?e, ?xs), [(addr a\<bullet>M(map Val vs), [])]), no_wait_locks)], h), empty)"
    from fvbody cisbody len vs
    have "bisim [] (blocks (this # pns, Class C # Ts, Addr a # vs, body)) (blocks1 (length ([] :: vname list)) (Class C # Ts) (compE1 (this # pns) body)) ?xs"
      by-(rule blocks_bisim, (fastsimp simp add: nth_Cons')+)
    with fv dabody len vs elbody rest show "red0_Red1_FWbase.mbisim ?s2 ?s3"
      apply(auto intro!: red0_Red1_FWbase.mbisimI split: split_if_asm)
      apply(auto simp add: bisim_red0_Red1_def blocks1_max_vars intro!: bisim_list.intros bisim_list1I)
      done
    show "(mbisim_Red1'_Red1 \<circ>\<^isub>B Red1_execd_FWbase.mbisim (compP1 P)) ?s3 ?s4"
    proof(rule bisim_composeI)
      from fv dabody len vs elbody rest
      show "mbisim_Red1'_Red1 ?s3 ?s3"
	by(fastsimp simp add: mbisim_Red1'_Red1_def lock_oks1_def el_loc_ok1_def contains_insync_conv intro!: ts_okI el_loc_ok_compE1 expr_locks_sync_ok split: split_if_asm)

      from len vs have "\<B> ?e 0" by(auto intro!: \<B>)
      with elbody have "compP1 P,?e,0,h \<turnstile> (?e, ?xs) \<leftrightarrow> ([], ?xs, 0, None)"
	by -(rule bisim1_refl, auto simp add: bsok_def)
      moreover have "bisim1_list1 (compP1 P) h (blocks1 0 (Class C#Ts) (compE1 (this # pns) body), Addr a # vs @ rest) ([] @ [(addr a\<bullet>M(map Val vs), [])]) None [([], Addr a # vs @ rest, C, M, 0)]"
      proof
	from rest len vs ha sees_method_decl_above[OF sees'] conf
	have "conf_f (compP2 (compP1 P)) h ([], TC0.ty\<^isub>l (Suc (length Ts + max_vars body)) (Class C # Ts) {..length Ts})
                    (compE2 (compE1 (this # pns) body) @ [Return]) ([], Addr a # vs @ rest, C, M, 0)"
	  unfolding conf_f_def2 apply- apply(rule conjI) apply simp
	  apply(rule conjI)
	  prefer 2
	  apply simp
	  apply(rule list_all2_all_nthI)
  	   apply(simp add: TC0.ty\<^isub>l_def)
	  apply(auto simp add: nth_Cons')
    	     apply(simp add: TC0.ty\<^isub>l_def compP2_def conf_def)
	    apply(simp only: TC0.ty\<^isub>l_def)
	    apply(subst nth_map, simp)
	    apply auto
	     apply(simp add: compP2_def)
	     apply(erule list_all2_nthD2)
	     apply clarsimp
	    apply(simp add: compP2_def)
	    apply(cases Ts, simp)
	    apply(simp del: list_all2_Cons2 list_all2_Cons1)
	    apply(drule_tac p="n - Suc 0" in list_all2_nthD2)
	     apply simp
	    apply(subgoal_tac "n=length Ts")
	     apply simp
	    apply simp
	   apply(auto simp add: TC0.ty\<^isub>l_def conf_def compP2_def)
	  done
	with hconf sees_method_compP[OF sees1, where f=compMb2] sees1
	show "compP2 (compP1 P),compTP (compP1 P) \<turnstile> (None, h, [([], Addr a # vs @ rest, C, M, 0)]) \<surd>"
	  apply(auto simp add: correct_state_def compP2_def compMb2_def)
	  apply(rule exI conjI|assumption)+
  	   apply(simp add: compTP_def)
	   apply(simp add: TC0.ty\<^isub>i'_def)
	  apply(auto simp add: conf_f_def2)
	  done
	from sees1 show "compP1 P \<turnstile> C sees M: Ts\<rightarrow>T = compE1 (this # pns) body in C" .
	from `\<B> ?e 0` elbody
	show "compP1 P,blocks1 0 (Class C#Ts) (compE1 (this # pns) body),0,h \<turnstile> (blocks1 0 (Class C#Ts) (compE1 (this # pns) body), Addr a # vs @ rest) \<leftrightarrow> ([], Addr a # vs @ rest, 0, None)"
	  by -(rule bisim1_refl, simp add: bsok_def)
	show "max_vars (blocks1 0 (Class C#Ts) (compE1 (this # pns) body)) \<le> length (Addr a # vs @ rest)"
	  using rest len vs by(simp add: blocks1_max_vars)
      qed simp
      then show "Red1_execd_FWbase.mbisim (compP1 P) ?s3 ?s4" using sees1 hconf sees ha vs pns
	by-(rule Red1_execd_FWbase.mbisimI,auto split: split_if_asm)
    qed
  qed
qed

fun exception :: "expr \<times> locals \<Rightarrow> addr option \<times> frame list"
where "exception (Throw a, xs) = (\<lfloor>a\<rfloor>, [])"
| "exception _ = (None, [])"

definition mexception :: "(addr,addr,expr\<times>locals,heap,addr) state \<Rightarrow> (addr,addr,addr option\<times>frame list,heap,addr) state"
where "mexception s \<equiv> (locks s, (\<lambda>t. case thr s t of \<lfloor>(e, ln)\<rfloor> \<Rightarrow> \<lfloor>(exception e, ln)\<rfloor> | None \<Rightarrow> None, shr s), wset s)"

interpretation red_red0_FWbase_aux: FWbisimulation_base_aux final_expr "mred P" final_expr0 "mred0 P" bisim_red_red0
  for P
by(unfold_locales)

interpretation red1_mexecd_FWbase_aux:
  FWbisimulation_base_aux final_expr1 "mred1 P" JVM_final "mexecd (compP2 P)" "wbisim1 P"
  for P
..

interpretation red0_Red1_FWbisim_base_aux: FWbisimulation_base_aux final_expr0 "mred0 P" final_expr1 "mred1' (compP1 P)" bisim_red0_Red1
  for P
..

lemma bisimJ2JVM_mfinal_mexception:
  assumes bisim: "bisimJ2JVM P s s'"
  and fin: "exec_mthr.mfinal s'"
  and tsNotEmpty: "thr s t \<noteq> None"
  shows "s' = mexception s"
proof -
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s) auto
  from bisim obtain s0 s1 where bisimJ0: "red_red0_FWbase.mbisim s s0"
    and bisim01: "red0_Red1_FWbase.mbisim s0 s1"
    and bisim1JVM: "Red1_execd_FWbase.mbisim (compP1 P) s1 s'"
    unfolding bisimJ2JVM_def by(fastsimp simp add: mbisim_Red1'_Red1_def)
  from bisimJ0 s have [simp]: "locks s0 = ls" "wset s0 = ws"
    and tbisimJ0: "\<And>t. red_red0_FWbase.tbisim (ts t) m (thr s0 t) (shr s0)"
    by(auto simp add: red_red0_FWbase.mbisim_def)
  from bisim01 have [simp]: "locks s1 = ls" "wset s1 = ws"
    and tbisim01: "\<And>t. red0_Red1_FWbase.tbisim (thr s0 t) (shr s0) (thr s1 t) (shr s1)"
    by(auto simp add: red0_Red1_FWbase.mbisim_def)
  from bisim1JVM have "locks s' = ls" "wset s' = ws"
    and tbisim1JVM: "\<And>t. Red1_execd_FWbase.tbisim (compP1 P) (thr s1 t) (shr s1) (thr s' t) (shr s')"
    by(auto simp add: Red1_execd_FWbase.mbisim_def)
  then obtain ts' m' where s': "s' = (ls, (ts', m'), ws)" by(cases s') fastsimp
  { fix t e x ln
    assume tst: "ts t = \<lfloor>((e, x), ln)\<rfloor>"
    from tbisimJ0[of t] tst obtain e' exs' where ts0t: "thr s0 t = \<lfloor>((e', exs'), ln)\<rfloor>"
      and bisimtJ0: "bisim_red_red0 ((e, x), m) ((e', exs'), shr s0)"
      by(auto simp add: red_red0_FWbase.tbisim_def)
    from tbisim01[of t] ts0t obtain e'' xs'' exs''
      where ts1t: "thr s1 t = \<lfloor>(((e'', xs''), exs''), ln)\<rfloor>"
      and bisimt01: "bisim_red0_Red1 ((e', exs'), shr s0) (((e'', xs''), exs''), shr s1)"
      by(auto simp add: red0_Red1_FWbase.tbisim_def)
    from tbisim1JVM[of t] ts1t s' obtain xcp frs
      where ts't: "ts' t = \<lfloor>((xcp, frs), ln)\<rfloor>" and [simp]: "m' = shr s1"
      and bisimt1JVM: "bisim1_list1 (compP1 P) m' (e'', xs'') exs'' xcp frs"
      by(fastsimp simp add: Red1_execd_FWbase.tbisim_def)

    from fin ts't s s' have [simp]: "frs = []" by(auto dest: exec_mthr.mfinalD)
    from bisimt1JVM have [simp]: "exs'' = []" by(auto elim: bisim1_list1.cases)
    from bisimt01 have [simp]: "exs' = []"
      by(auto simp add: bisim_red0_Red1_def elim!: bisim_list1E elim: bisim_list.cases)
    from bisimtJ0 have fine: "final e" by(auto elim: bisim_red_red0.cases)
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
    with red_red0_FWbase.mbisim_thrNone_eq[OF bisimJ0, of t] s have "thr s0 t = None" by simp
    with bisim01 have "thr s1 t = None" by(auto simp add: red0_Red1_FWbase.mbisim_thrNone_eq)
    with bisim1JVM s' have "ts' t = None" by(simp add: Red1_execd_FWbase.mbisim_thrNone_eq) }
  ultimately show ?thesis using s s' tsNotEmpty by(auto simp add: mexception_def expand_fun_eq)
qed  

lemma (in multithreaded_base) \<tau>rtrancl3p_redT_thread_not_disappear:
  assumes "\<tau>trsys.\<tau>rtrancl3p redT \<tau>move s ttas s'" "thr s t \<noteq> None"
  shows "thr s' t \<noteq> None"
proof -
  interpret T: \<tau>trsys redT \<tau>move .
  show ?thesis
  proof
    assume "thr s' t = None"
    with `\<tau>trsys.\<tau>rtrancl3p redT \<tau>move s ttas s'` have "thr s t = None"
      by(induct rule: T.\<tau>rtrancl3p.induct)(auto simp add: split_paired_all dest: redT_thread_not_disappear)
    with `thr s t \<noteq> None` show False by contradiction
  qed
qed

lemma list_all2_op_eq [simp]: -- "Move to Aux"
  "list_all2 op = xs ys \<longleftrightarrow> xs = ys"
by(induct xs arbitrary: ys)(auto simp add: list_all2_Cons1)

lemma list_all2_bisim_composeI: -- "Move to Bisimulation"
  "\<lbrakk> list_all2 A xs ys; list_all2 B ys zs \<rbrakk>
  \<Longrightarrow> list_all2 (A \<circ>\<^isub>B B) xs zs"
by(rule list_all2_trans)(auto intro: bisim_composeI)+

lemma J2JVM_correct:
  assumes wf: "wf_J_prog P"
  and sees': "P \<turnstile> D sees M:Ts\<rightarrow>T=(pns,body) in C"
  and vs: "length vs = length pns" and conf: "P,h \<turnstile> vs [:\<le>] Ts" and hconf: "P \<turnstile> h \<surd>"
  and rest: "length rest = max_vars body"
  and ha: "h a = \<lfloor>Obj D fs\<rfloor>"
  and s: "s = (\<lambda>\<^isup>f None, ([t \<mapsto> ((blocks (this#pns, Class C#Ts, Addr a#vs, body), empty), no_wait_locks)], h), empty)"
  and comps: "cs = (\<lambda>\<^isup>f None, ([t \<mapsto> ((None, [([], Addr a # vs @ rest, C, M, 0)]), no_wait_locks)], h), empty)"
  shows
  "\<lbrakk> red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s'; red_mthr.mfinal s' \<rbrakk>
  \<Longrightarrow> \<exists>ttas'. mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' (mexception s') \<and>
             bisimulation_base.Tlsim (tlsimJ2JVM P) ttas ttas'" (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?thesis1")
  and
  "\<lbrakk> mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'; exec_mthr.mfinal cs' \<rbrakk>
  \<Longrightarrow> \<exists>s' ttas. red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s' \<and> mexception s' = cs' \<and>
               bisimulation_base.Tlsim (tlsimJ2JVM P) ttas ttas'" (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?thesis2")
  and
  "red_\<tau>mthr.mthr.\<tau>inf_step P s Ttas
  \<Longrightarrow> \<exists>Ttas'. mexecd_\<tau>mthr.mthr.\<tau>inf_step (J2JVM P) cs Ttas' \<and> bisimulation_base.Tlsiml (tlsimJ2JVM P) Ttas Ttas'"
  (is "_ \<Longrightarrow> ?thesis3")
  and
  "mexecd_\<tau>mthr.mthr.\<tau>inf_step (J2JVM P) cs Ttas'
  \<Longrightarrow> \<exists>Ttas. red_\<tau>mthr.mthr.\<tau>inf_step P s Ttas \<and> bisimulation_base.Tlsiml (tlsimJ2JVM P) Ttas Ttas'"
  (is "_ \<Longrightarrow> ?thesis4")
  and
  "\<lbrakk> red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s'; multithreaded_base.deadlock final_expr (mred P) s' \<rbrakk>
  \<Longrightarrow> \<exists>cs' ttas'. mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs' \<and>
                 multithreaded_base.deadlock JVM_final (mexecd (J2JVM P)) cs' \<and> bisimJ2JVM P s' cs' \<and>
                 bisimulation_base.Tlsim (tlsimJ2JVM P) ttas ttas'" (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?thesis5")
  and
  "\<lbrakk> mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'; multithreaded_base.deadlock JVM_final (mexecd (J2JVM P)) cs' \<rbrakk>
  \<Longrightarrow> \<exists>s' ttas. red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s' \<and> multithreaded_base.deadlock final_expr (mred P) s' \<and> bisimJ2JVM P s' cs' \<and>
               bisimulation_base.Tlsim (tlsimJ2JVM P) ttas ttas'" (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?thesis6")
proof -
  interpret delay_bisimulation_diverge_final "mredT P" "execd_mthr.redT (J2JVM P)" "bisimJ2JVM P" "tlsimJ2JVM P" "red_red0_FWwbase.m\<tau>move1 P" "Red1_execd_FWwbase.m\<tau>move2 (compP1 P)" red_mthr.mfinal exec_mthr.mfinal
    using wf by(rule bisimJ2JVM_weak_bisim)

  from wf sees' vs conf hconf rest ha have bisim: "bisimJ2JVM P s cs" unfolding s comps by(rule bisimJ2JVM_start)
  { assume red: "red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s'"
    and fin: "red_mthr.mfinal s'"
    
    from final_simulation1[OF bisim red fin] obtain cs' ttas'
      where exec: "mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'"
      and bisim': "bisimJ2JVM P s' cs'"
      and fin': "exec_mthr.mfinal cs'" and tlsim: "bisimulation_base.Tlsim (tlsimJ2JVM P) ttas ttas'"
      unfolding J2JVM_def o_def by(clarify)
    moreover from red s have "thr s' t \<noteq> None" by -(erule multithreaded_base.\<tau>rtrancl3p_redT_thread_not_disappear, simp)
    with bisim' fin' have [simp]: "cs' = mexception s'" by(intro bisimJ2JVM_mfinal_mexception disjI1)
    ultimately show ?thesis1 by blast
  next
    assume exec: "mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'"
      and fin: "exec_mthr.mfinal cs'"
    from final_simulation2[OF bisim, folded J2JVM_def[THEN meta_eq_to_obj_eq, unfolded expand_fun_eq, THEN spec, unfolded o_def], OF exec fin]
    obtain s' ttas where red: "red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s'"
      and bisim': "bisimJ2JVM P s' cs'" and fin': "red_mthr.mfinal s'"
      and tlsim: "bisimulation_base.Tlsim (tlsimJ2JVM P) ttas ttas'" by blast
    moreover from red s have "thr s' t \<noteq> None" by -(erule multithreaded_base.\<tau>rtrancl3p_redT_thread_not_disappear, simp)
    with bisim' fin have [simp]: "cs' = mexception s'" by(intro bisimJ2JVM_mfinal_mexception disjI2)
    ultimately show ?thesis2 by blast
  next
    assume "red_\<tau>mthr.mthr.\<tau>inf_step P s Ttas"
    from simulation1_\<tau>inf_step[OF this bisim] show ?thesis3
      unfolding J2JVM_def o_def .
  next
    assume "mexecd_\<tau>mthr.mthr.\<tau>inf_step (J2JVM P) cs Ttas'"
    thus ?thesis4 using bisim
      by -(rule simulation2_\<tau>inf_step, auto simp add: J2JVM_def o_def)
  }

next
  interpret b0: FWdelay_bisimulation_measure final_expr "mred P" final_expr0 "mred0 P" bisim_red_red0 "\<tau>MOVE P" "\<tau>MOVE0 P" "\<lambda>e e'. False" "\<lambda>((e, es), h) ((e, es'), h). length es < length es'"
    by(rule red_red0_FWbisim[OF wf_prog_wwf_prog[OF wf]])
  interpret b01: FWdelay_bisimulation_measure final_expr0 "mred0 P" final_expr1 "mred1' (compP1 P)" bisim_red0_Red1 "\<tau>MOVE0 P" "\<tau>MOVE1 (compP1 P)" "\<lambda>es es'. False" "\<lambda>(((e', xs'), exs'), h') (((e, xs), exs), h). countInitBlock e'< countInitBlock e"
    by(rule red0_Red1'_FWweak_bisim[OF wf])
  interpret b11: bisimulation_into_delay "Red1'_mthr.redT (compP1 P)" "Red1_mthr.redT (compP1 P)" "mbisim_Red1'_Red1" "op =" "Red1'_\<tau>mthr.m\<tau>move (compP1 P)" "Red1_\<tau>mthr.m\<tau>move (compP1 P)"
    using compP1_pres_wf[OF wf] by(rule Red1'_Red1_bisim_into_weak)
  interpret b12: FWdelay_bisimulation_measure final_expr1 "mred1 (compP1 P)" JVM_final "mexecd (compP2 (compP1 P))"
                                   "wbisim1 (compP1 P)" "\<tau>MOVE1 (compP1 P)" "\<tau>MOVE2 (compP2 (compP1 P))"
                                   "\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e'"
                                   "\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 (compP1 P)) xcpfrs xcpfrs'"
    using compP1_pres_wf[OF wf] by(intro Red1_mexecd_FWweak_bisim)

  from wf sees' vs conf hconf rest ha have bisim: "bisimJ2JVM P s cs" unfolding s comps by(rule bisimJ2JVM_start)
  from bisim obtain s0 s1 s1' where bisim0: "red_red0_FWbase.mbisim s s0"
    and bisim01: "red0_Red1_FWbase.mbisim s0 s1"
    and bisim11: "mbisim_Red1'_Red1 s1 s1'"
    and bisim12: "Red1_execd_FWbase.mbisim (compP1 P) s1' cs"
    unfolding bisimJ2JVM_def by auto
  from bisim11 have "s1' = s1" by(simp add: mbisim_Red1'_Red1_def)
  {
    assume red: "red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s'"
      and dead: "multithreaded_base.deadlock final_expr (mred P) s'"
    from b0.mthr.simulation1_\<tau>rtrancl3p[OF red bisim0]
    obtain ttas0 s0' where "red0_\<tau>mthr.mthr.\<tau>rtrancl3p P s0 ttas0 s0'"
      and "red_red0_FWbase.mbisim s' s0'"
      and tlsim0: "bisimulation_base.Tlsim red_red0_FWbase.mta_bisim ttas ttas0" by auto
    from b0.deadlock1_imp_\<tau>s_deadlock2[OF `red_red0_FWbase.mbisim s' s0'` dead]
    obtain s0'' where "red0_\<tau>mthr.mthr.silent_moves P s0' s0''"
      and bisim0': "red_red0_FWbase.mbisim s' s0''"
      and dead0: "multithreaded_base.deadlock final_expr0 (mred0 P) s0''" by auto
    from `red0_\<tau>mthr.mthr.\<tau>rtrancl3p P s0 ttas0 s0'` `red0_\<tau>mthr.mthr.silent_moves P s0' s0''`
    have "red0_\<tau>mthr.mthr.\<tau>rtrancl3p P s0 (ttas0 @ []) s0''"
      by(rule red0_\<tau>mthr.mthr.\<tau>rtrancl3p_trans[OF _ red0_\<tau>mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    from b01.mthr.simulation1_\<tau>rtrancl3p[OF this bisim01]
    obtain ttas1 s1'' where "Red1'_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 ttas1 s1''"
      and "red0_Red1_FWbase.mbisim s0'' s1''"
      and tlsim01: "bisimulation_base.Tlsim red0_Red1_FWbase.mta_bisim ttas0 ttas1" by auto
    from b01.deadlock1_imp_\<tau>s_deadlock2[OF `red0_Red1_FWbase.mbisim s0'' s1''` dead0]
    obtain s1''' where "Red1'_\<tau>mthr.mthr.silent_moves (compP1 P) s1'' s1'''"
      and dead1: "multithreaded_base.deadlock final_expr1 (mred1' (compP1 P)) s1'''"
      and bisim01': "red0_Red1_FWbase.mbisim s0'' s1'''" by auto
    from `Red1'_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 ttas1 s1''` `Red1'_\<tau>mthr.mthr.silent_moves (compP1 P) s1'' s1'''`
    have "Red1'_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 (ttas1 @ []) s1'''"
      by(rule Red1'_\<tau>mthr.mthr.\<tau>rtrancl3p_trans[OF _ Red1'_\<tau>mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    from b11.simulation1_\<tau>rtrancl3p[OF this bisim11]
    obtain s1'''' where "Red1_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' ttas1 s1''''"
      and bisim11': "mbisim_Red1'_Red1 s1''' s1''''" by auto
    from b12.mthr.simulation1_\<tau>rtrancl3p[OF `Red1_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' ttas1 s1''''` bisim12]
    obtain ttas' cs' where "mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs ttas' cs'"
      and "Red1_execd_FWbase.mbisim (compP1 P) s1'''' cs'"
      and tlsim12: "list_all2 (Red1_execd_FWbase.mta_bisim (compP1 P)) ttas1 ttas'" by(auto)
    from bisim11' have "s1''' = s1''''" by(simp add: mbisim_Red1'_Red1_def)
    with dead1 have "multithreaded_base.deadlock final_expr1 (mred1 (compP1 P)) s1''''"
      by(simp add: Red1_Red1'_deadlock_inv)
    from b12.deadlock1_imp_\<tau>s_deadlock2[OF `Red1_execd_FWbase.mbisim (compP1 P) s1'''' cs'` this]
    obtain cs'' where "mexecd_\<tau>mthr.mthr.silent_moves (compP2 (compP1 P)) cs' cs''"
      and bisim12': "Red1_execd_FWbase.mbisim (compP1 P) s1'''' cs''"
      and dead': "multithreaded_base.deadlock JVM_final (mexecd (compP2 (compP1 P))) cs''" by auto
    from `mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs ttas' cs'` `mexecd_\<tau>mthr.mthr.silent_moves (compP2 (compP1 P)) cs' cs''`
    have "mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs (ttas' @ []) cs''"
      by(rule mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p_trans[OF _ mexecd_\<tau>mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    moreover from bisim0' bisim01' bisim11' bisim12' have "bisimJ2JVM P s' cs''"
      by(auto simp add: bisimJ2JVM_def J2JVM_def o_def intro: bisim_composeI)
    moreover from tlsim0 tlsim01 tlsim12
    have "list_all2 (tlsimJ2JVM P) ttas ttas'"
      by(auto intro!: list_all2_bisim_composeI simp add: tlsimJ2JVM_def)
    ultimately show ?thesis5 using dead' unfolding J2JVM_def o_def
      by-(rule exI conjI|assumption|simp)+
  next
    assume "mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (J2JVM P) cs ttas' cs'"
      and "multithreaded_base.deadlock JVM_final (mexecd (J2JVM P)) cs'"
    hence "mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs ttas' cs'"
      and dead: "multithreaded_base.deadlock JVM_final (mexecd (compP2 (compP1 P))) cs'"
      by(simp_all add: J2JVM_def o_def)
    from b12.mthr.simulation2_\<tau>rtrancl3p[OF `mexecd_\<tau>mthr.mthr.\<tau>rtrancl3p (compP2 (compP1 P)) cs ttas' cs'` bisim12]
    obtain ttas1 s1'' where "Red1_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' ttas1 s1''"
      and "Red1_execd_FWbase.mbisim (compP1 P) s1'' cs'"
      and tlsim12: "list_all2 (Red1_execd_FWbase.mta_bisim (compP1 P)) ttas1 ttas'" by(auto)
    from b12.deadlock2_imp_\<tau>s_deadlock1[OF `Red1_execd_FWbase.mbisim (compP1 P) s1'' cs'` dead]
    obtain s1''' where "Red1_\<tau>mthr.mthr.silent_moves (compP1 P) s1'' s1'''"
      and dead1: "multithreaded_base.deadlock final_expr1 (mred1 (compP1 P)) s1'''"
      and bisim12': "Red1_execd_FWbase.mbisim (compP1 P) s1''' cs'" by auto
    from `Red1_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' ttas1 s1''` `Red1_\<tau>mthr.mthr.silent_moves (compP1 P) s1'' s1'''`
    have "Red1_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1' (ttas1 @ []) s1'''"
      by(rule Red1_\<tau>mthr.mthr.\<tau>rtrancl3p_trans[OF _ Red1_\<tau>mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    from b11.simulation2_\<tau>rtrancl3p[OF this bisim11]
    obtain s1'''' where "Red1'_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 ttas1 s1''''"
      and bisim11': "mbisim_Red1'_Red1 s1'''' s1'''" by(auto)
    from b01.mthr.simulation2_\<tau>rtrancl3p[OF `Red1'_\<tau>mthr.mthr.\<tau>rtrancl3p (compP1 P) s1 ttas1 s1''''` bisim01]
    obtain ttas0 s0' where "red0_\<tau>mthr.mthr.\<tau>rtrancl3p P s0 ttas0 s0'"
      and "red0_Red1_FWbase.mbisim s0' s1''''"
      and tlsim01: "bisimulation_base.Tlsim red0_Red1_FWbase.mta_bisim ttas0 ttas1" by auto
    from bisim11' have "s1''' = s1''''" by(simp add: mbisim_Red1'_Red1_def)
    with dead1 have "multithreaded_base.deadlock final_expr1 (mred1' (compP1 P)) s1''''"
      by(simp add: Red1_Red1'_deadlock_inv)
    from b01.deadlock2_imp_\<tau>s_deadlock1[OF `red0_Red1_FWbase.mbisim s0' s1''''` this]
    obtain s0'' where "red0_\<tau>mthr.mthr.silent_moves P s0' s0''"
      and bisim01': "red0_Red1_FWbase.mbisim s0'' s1''''"
      and dead0: "multithreaded_base.deadlock final_expr0 (mred0 P) s0''" by auto
    from `red0_\<tau>mthr.mthr.\<tau>rtrancl3p P s0 ttas0 s0'` `red0_\<tau>mthr.mthr.silent_moves P s0' s0''`
    have "red0_\<tau>mthr.mthr.\<tau>rtrancl3p P s0 (ttas0 @ []) s0''"
      by(rule red0_\<tau>mthr.mthr.\<tau>rtrancl3p_trans[OF _ red0_\<tau>mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    from b0.mthr.simulation2_\<tau>rtrancl3p[OF this bisim0]
    obtain ttas s' where "red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s'"
      and "red_red0_FWbase.mbisim s' s0''"
      and tlsim0: "bisimulation_base.Tlsim red_red0_FWbase.mta_bisim ttas ttas0" by auto
    from b0.deadlock2_imp_\<tau>s_deadlock1[OF `red_red0_FWbase.mbisim s' s0''` dead0]
    obtain s'' where "red_\<tau>mthr.mthr.silent_moves P s' s''"
      and dead': "multithreaded_base.deadlock final_expr (mred P) s''"
      and bisim0': "red_red0_FWbase.mbisim s'' s0''" by auto
    from `red_\<tau>mthr.mthr.\<tau>rtrancl3p P s ttas s'` `red_\<tau>mthr.mthr.silent_moves P s' s''`
    have "red_\<tau>mthr.mthr.\<tau>rtrancl3p P s (ttas @ []) s''"
      by(rule red_\<tau>mthr.mthr.\<tau>rtrancl3p_trans[OF _ red_\<tau>mthr.mthr.silent_moves_into_\<tau>rtrancl3p])
    moreover from bisim0' bisim01' bisim11' bisim12' have "bisimJ2JVM P s'' cs'"
      by(auto simp add: bisimJ2JVM_def J2JVM_def o_def intro: bisim_composeI)
    moreover from tlsim0 tlsim01 tlsim12
    have "list_all2 (tlsimJ2JVM P) ttas ttas'"
      by(auto intro!: list_all2_bisim_composeI simp add: tlsimJ2JVM_def)
    ultimately show ?thesis6 using dead'
      by-(rule exI conjI|assumption|simp)+
  }
qed

lemma wt_J2JVM: "wf_J_prog P \<Longrightarrow> wf_jvm_prog (J2JVM P)"
unfolding J2JVM_def o_def
by(rule wt_compP2)(rule compP1_pres_wf)

end