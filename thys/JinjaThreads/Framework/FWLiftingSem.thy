(*  Title:      JinjaThreads/Framework/FWLiftingSem.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantic properties of lifted predicates} *}

theory FWLiftingSem imports FWSemantics FWLifting begin

context multithreaded begin

lemma redT_preserves_ts_inv_ok:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; ts_inv_ok (thr s) I \<rbrakk>
  \<Longrightarrow> ts_inv_ok (thr s') (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)"
by(erule redT.cases)(auto intro: ts_inv_ok_upd_invs ts_inv_ok_upd_ts redT_updTs_Some)

lemma RedT_preserves_ts_inv_ok:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ts_inv_ok (thr s) I \<rbrakk>
  \<Longrightarrow> ts_inv_ok (thr s') (upd_invs I Q (\<down>map (thr_a \<circ> snd) ttas\<down>))"
by(induct rule: RedT_induct)(auto intro: redT_preserves_ts_inv_ok)

lemma redT_upd_inv_ext:
  fixes I :: "'t \<rightharpoonup> 'i"
  shows "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; ts_inv_ok (thr s) I \<rbrakk> \<Longrightarrow> I \<unlhd> upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
by(erule redT.cases, auto intro: ts_inv_ok_inv_ext_upd_invs)

lemma RedT_upd_inv_ext:
  fixes I :: "'t \<rightharpoonup> 'i"
  shows "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ts_inv_ok (thr s) I \<rbrakk>
         \<Longrightarrow> I \<unlhd> upd_invs I P (\<down>map (thr_a \<circ> snd) ttas\<down>)"
proof(induct rule: RedT_induct)
  case refl thus ?case by simp
next
  case (step S TTAS S' T TA S'')
  hence "ts_inv_ok (thr S') (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>))"
    by -(erule RedT_preserves_ts_inv_ok, assumption)
  hence "upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>) \<unlhd> upd_invs (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>)) P \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>" using step
    by -(erule redT_upd_inv_ext)
  with step show ?case
    apply(simp)
    apply(erule inv_ext_trans)
    by(simp add: comp_def)
qed

end

locale lifting_wf = multithreaded +
  fixes P :: "'x \<Rightarrow> 'm \<Rightarrow> bool"
  assumes preserves_red: "\<lbrakk> r (x, m) ta (x', m'); P x m \<rbrakk> \<Longrightarrow> P x' m'"
  assumes preserves_NewThread: "\<lbrakk> r (x, m) ta (x', m'); P x m; NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> P x'' m'"
  assumes preserves_other: "\<lbrakk> r (x, m) ta (x', m'); P x m; P x'' m \<rbrakk> \<Longrightarrow> P x'' m'"
begin


lemma redT_preserves:
  assumes redT: "s -t\<triangleright>ta\<rightarrow> s'"
  and esokQ: "ts_ok P (thr s) (shr s)"
  shows "ts_ok P (thr s') (shr s')"
proof(rule ts_okI)
  fix T X LN
  assume "thr s' T = \<lfloor>(X, LN)\<rfloor>"
  moreover obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by(cases s, auto)
  moreover obtain ls' ts' m' ws' where s' [simp]: "s' = (ls', (ts', m'), ws')" by(cases s', auto)
  ultimately have es't': "ts' T = \<lfloor>(X, LN)\<rfloor>" by auto
  obtain las tas cas was where ta: "ta = (las, tas, cas, was)" by(cases ta, auto)
  from redT show "P X (shr s')"
  proof(induct rule: redT_elims)
    case (normal x x')
    with ta have red: "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
      and est: "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and lota: "lock_ok_las ls t las"
      and cctta: "thread_oks ts m' tas"
      and cdta: "cond_action_oks (ls, (ts, m), ws) t cas"
      and wst: "ws t = None"
      and ls': "ls' = redT_updLs ls t las"
      and es': "ts' = redT_updTs ts tas(t \<mapsto> (x', redT_updLns ls t no_wait_locks las))"
      and ws': "ws' = redT_updWs ws t was"
      by(auto)
    from est esokQ have qex: "P x m" by(auto dest: ts_okD)
    show "P X (shr s')"
    proof(cases "t = T")
      assume tt': "t = T"
      from red qex have "P x' m'" by(rule preserves_red)
      moreover from es't' es' tt' have "X = x'" by(simp)
      ultimately show ?thesis by simp
    next
      assume tt': "t \<noteq> T"
      show ?thesis
      proof(cases "ts T")
	assume esT: "ts T = None"
	with es't' est redT ta have "NewThread T X m' \<in> set tas"
	  by(auto dest!: redT_new_thread)
	thus ?thesis using red qex ta
	  by(auto intro: preserves_NewThread)
      next
	fix a
	assume "ts T = \<lfloor>a\<rfloor>"
	obtain x ln where [simp]: "a = (x, ln)" by (cases a, auto)
	from `ts T = \<lfloor>a\<rfloor>` have esT: "ts T = \<lfloor>(x, ln)\<rfloor>" by simp
	with redT tt' esT have "ts' T = \<lfloor>(x, ln)\<rfloor>"
	  by(auto elim: redT_ts_Some_inv)
	with es't' have "X = x" by auto
	moreover
	from esT esokQ have "P x m" by(auto dest: ts_okD)
	with qex have "P x m'" by -(rule preserves_other[OF red])
	ultimately show ?thesis by simp
      qed
    qed
  next
    fix x ln
    assume "shr s' = shr s" "thr s' = thr s(t \<mapsto> (x, no_wait_locks))" 
      and "thr s t = \<lfloor>(x, ln)\<rfloor>"
    hence [simp]: "m = m'" "ts' = ts(t \<mapsto> (x, no_wait_locks))" by(auto)
    show ?thesis
    proof(cases "T = t")
      case True 
      note [simp] = this
      with es't' have "X = x" by(simp)
      with esokQ `thr s t = \<lfloor>(x, ln)\<rfloor>` 
      show ?thesis by(auto dest!: ts_okD)
    next
      case False
      with es't' have "ts T = \<lfloor>(X, LN)\<rfloor>" by(simp)
      with esokQ show ?thesis by(auto dest: ts_okD)
    qed
  qed
qed

lemma RedT_preserves:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
apply(erule RedT_lift_preserveD, assumption)
by(fastsimp elim: redT_preserves)

end

lemma lifting_wf_Const [intro!]: "lifting_wf r (\<lambda>x m. k)" ..

locale lifting_inv = lifting_wf final r Q +
  fixes P :: "'i \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
  assumes invariant_red: "\<lbrakk> r (x, m) ta (x', m'); P i x m; Q x m \<rbrakk> \<Longrightarrow> P i x' m'"
  assumes invariant_NewThread: "\<lbrakk> r (x, m) ta (x', m'); P i x m; Q x m; NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>i''. P i'' x'' m'"
  assumes invariant_other: "\<lbrakk> r (x, m) ta (x', m'); P i x m; Q x m; P i'' x'' m; Q x'' m \<rbrakk> \<Longrightarrow> P i'' x'' m'"
begin

lemma redT_invariant:
  assumes redT: "s -t\<triangleright>ta\<rightarrow> s'"
  and esinvP: "ts_inv P I (thr s) (shr s)"
  and esokQ: "ts_ok Q (thr s) (shr s)"
  shows "ts_inv P (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (thr s') (shr s')"
proof(rule ts_invI)
  fix T X LN
  assume "thr s' T = \<lfloor>(X, LN)\<rfloor>"
  moreover obtain ls ts m ws where s [simp]: "s = (ls, (ts, m), ws)" by(cases s, auto)
  moreover obtain ls' ts' m' ws' where s' [simp]: "s' = (ls', (ts', m'), ws')" by(cases s', auto)
  ultimately have es't': "ts' T = \<lfloor>(X, LN)\<rfloor>" by auto
  obtain las tas cas was where ta: "ta = (las, tas, cas, was)" by (cases ta, auto)
  from redT show "\<exists>i. upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>i\<rfloor> \<and> P i X (shr s')"
  proof(induct rule: redT_elims)
    case (normal x x')
    with ta have red: "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
      and est: "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and lota: "lock_ok_las ls t las"
      and cctta: "thread_oks ts m' tas"
      and cdta: "cond_action_oks (ls, (ts, m), ws) t cas"
      and wst: "ws t = None"
      and ls': "ls' = redT_updLs ls t las"
      and es': "ts' = redT_updTs ts tas(t \<mapsto> (x', redT_updLns ls t no_wait_locks las))"
      and ws': "ws' = redT_updWs ws t was"
      by(auto)
    from est esinvP obtain i where Iti: "I t = \<lfloor>i\<rfloor>" and qiex: "P i x m"
      by(auto dest: ts_invD)
    from est esokQ Iti have rex: "Q x m" by(auto dest!: ts_okD)
    show ?thesis
    proof(cases "t = T")
      assume tT: "t = T"
      from qiex red rex have "P i x' m'"
	by -(rule invariant_red)
      moreover
      from tT est cctta Iti have "upd_invs I P tas t = \<lfloor>i\<rfloor>"
	by(auto intro: upd_invs_Some) 
      moreover
      from es't' es' tT have "X = x'" by simp
      ultimately show ?thesis using tT ta by clarsimp
    next
      assume tT: "t \<noteq> T"
      show ?thesis
      proof(cases "ts T")
	assume esT: "ts T = None" 
	with es't' est redT ta have nt: "NewThread T X m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
	  by -(auto dest: redT_new_thread)
	with red qiex rex have i: "\<exists>i''. P i'' X m'"
	  by(auto intro!: invariant_NewThread)
	hence "P (SOME i. P i X m') X m'"
	  by-(rule someI_ex)
	with nt cctta ta show ?thesis by (auto intro: SOME_new_thread_upd_invs) 
      next
	fix a
	assume "ts T = \<lfloor>a\<rfloor>"
	obtain x ln where [simp]: "a = (x, ln)" by(cases a, auto)
	with `ts T = \<lfloor>a\<rfloor>` have esT: "ts T = \<lfloor>(x, ln)\<rfloor>" by simp
	with redT tT have "ts' T = \<lfloor>(x, ln)\<rfloor>" by(auto dest: redT_ts_Some_inv)
	with es't' have "X = x" by auto
	moreover
	from esT esinvP obtain i' where i': "I T = \<lfloor>i'\<rfloor>" and qi'ex: "P i' x m"
	  by(auto dest: ts_invD)
	from esT esokQ have "Q x m" by (auto dest: ts_okD)
	hence "P i' x m'" using red qiex rex qi'ex
	  by(auto intro: invariant_other)
	moreover
	have "upd_invs I P tas T = \<lfloor>i'\<rfloor>" using i'
	  by(simp add: upd_invs_Some_eq[OF cctta, OF esT])
	ultimately show ?thesis using ta by auto
      qed
    qed
  next
    case (acquire x ln)
    hence [simp]: "m' = m" "ta = \<epsilon>" "ts' = ts(t \<mapsto> (x, no_wait_locks))" by auto
    show ?thesis
    proof(cases "T = t")
      case True
      with `thr s t = \<lfloor>(x, ln)\<rfloor>` es't'
      have [simp]: "X = x" by(simp)
      from True `thr s t = \<lfloor>(x, ln)\<rfloor>` `ts_inv P I (thr s) (shr s)`
      obtain i where "I t = \<lfloor>i\<rfloor>" and "P i x m" by(auto dest: ts_invD)
      with True show ?thesis by(simp)
    next
      case False
      with es't' `ts_inv P I (thr s) (shr s)`
      obtain i where "I T = \<lfloor>i\<rfloor>" and "P i X (shr s)" by(auto dest: ts_invD)
      thus ?thesis by simp
    qed
  qed
qed


lemma RedT_invariant:
  assumes RedT: "s -\<triangleright>ttas\<rightarrow>* s'"
  and esinvQ: "ts_inv P I (thr s) (shr s)"
  and esokR: "ts_ok Q (thr s) (shr s)"
  shows "ts_inv P (upd_invs I P (\<down>map (thr_a \<circ> snd) ttas\<down>)) (thr s') (shr s')"
using RedT esinvQ esokR
proof(induct rule: RedT_induct)
  case refl thus ?case by(simp (no_asm))
next
  case (step S TTAS S' T TA S'')
  note IH = `\<lbrakk>ts_inv P I (thr S) (shr S); ts_ok Q (thr S) (shr S)\<rbrakk> 
             \<Longrightarrow> ts_inv P (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>)) (thr S') (shr S')`
  with `ts_inv P I (thr S) (shr S)` `ts_ok Q (thr S) (shr S)`
  have "ts_inv P (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>)) (thr S') (shr S')" by blast
  moreover from `S -\<triangleright>TTAS\<rightarrow>* S'` `ts_ok Q (thr S) (shr S)`
  have "ts_ok Q (thr S') (shr S')" by(rule RedT_preserves)
  ultimately have "ts_inv P (upd_invs (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>)) P \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>) (thr S'') (shr S'')"
    using `S' -T\<triangleright>TA\<rightarrow> S''`
    by -(rule redT_invariant)
  thus ?case by(simp add: comp_def)
qed

end


end
