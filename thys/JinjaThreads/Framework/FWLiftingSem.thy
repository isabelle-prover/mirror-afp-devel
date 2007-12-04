(*  Title:      JinjaThreads/Framework/FWLiftingSem.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantic properties of lifted predicates} *}

theory FWLiftingSem imports FWSemantics FWLifting begin

context multithreaded begin

lemma redT_preserves_ts_inv_ok:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>;
     ts_inv_ok ts I \<rbrakk>
  \<Longrightarrow> ts_inv_ok ts' (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)"
apply(erule redT.cases, clarsimp)
apply(rule ts_inv_ok_upd_invs)
by(erule ts_inv_ok_upd_ts)


lemma RedT_preserves_ts_inv_ok:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>;
     ts_inv_ok ts I \<rbrakk>
  \<Longrightarrow> ts_inv_ok ts' (upd_invs I Q (\<down>map (thr_a \<circ> snd) ttas\<down>))"
apply(induct rule: RedT_induct4)
apply(auto intro: redT_preserves_ts_inv_ok simp del: thr_a_def)
done


lemma redT_upd_inv_ext:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>;
     ts_inv_ok ts I \<rbrakk>
  \<Longrightarrow> (I::('t \<rightharpoonup> 'i)) \<unlhd> upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
apply(erule redT.cases, clarsimp)
by(rule ts_inv_ok_inv_ext_upd_invs)

lemma RedT_upd_inv_ext:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>;
     ts_inv_ok ts I \<rbrakk>
  \<Longrightarrow> (I::('t \<rightharpoonup> 'i)) \<unlhd> upd_invs I P (\<down>map (thr_a \<circ> snd) ttas\<down>)"
proof(induct rule: RedT_induct4)
  case refl thus ?case by simp
next
  case (step LS TS M WS TTAS LS' TS' M' WS' T TA LS'' TS'' M'' WS'')
  hence "ts_inv_ok TS' (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>))"
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
  assumes preserves_red: "\<lbrakk> ((x, m), ta, x', m') \<in> r; P x m \<rbrakk> \<Longrightarrow> P x' m'"
  assumes preserves_NewThread: "\<lbrakk> ((x, m), ta, x', m') \<in> r; P x m; NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> P x'' m'"
  assumes preserves_other: "\<lbrakk> ((x, m), ta, x', m') \<in> r; P x m; P x'' m \<rbrakk> \<Longrightarrow> P x'' m'"
begin

lemma redT_preserves:
  assumes redT: "\<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>"
  and esokQ: "ts_ok P ts m"
  shows "ts_ok P ts' m'"
proof(rule ts_okI)
  fix T X
  assume es't': "ts' T = \<lfloor>X\<rfloor>"
  obtain las tas was where ta: "ta = (las, tas, was)" by(cases ta, auto)
  with redT obtain x x'
    where red: "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
    and est: "ts t = \<lfloor>x\<rfloor>"
    and lota: "lock_ok_las ls t las"
    and cctta: "thread_oks ts m' tas"
    and wst: "ws t = None"
    and ls': "ls' = redT_updLs ls t las"
    and es': "ts' = redT_updTs (ts(t \<mapsto> x')) tas"
    and ws': "ws' = redT_updWs ws t was"
    by(auto elim!: redT.cases)
  from est esokQ have qex: "P x m" by-(erule ts_okD)
  show "P X m'"
  proof(cases "t = T")
    assume tt': "t = T"
    from red qex have "P x' m'"
      by(rule preserves_red)
    moreover from es't' es' tt'
    have "redT_updTs (ts(T \<mapsto> x')) tas T = \<lfloor>X\<rfloor>"
      by(auto)
    hence "((redT_updTs ts tas)(T \<mapsto> x')) T = \<lfloor>X\<rfloor>"
      by(simp only: redT_updTs_upd[OF est cctta] tt'[THEN sym])
    hence "X = x'" by(auto)
    ultimately show ?thesis by simp
  next
    assume tt': "t \<noteq> T"
    show ?thesis
    proof(cases "ts T")
      assume esT: "ts T = None"
      with es't' est redT ta have "NewThread T X m' \<in> set tas"
	by(auto dest!: redT_new_thread)
      thus "P X m'" using red qex ta
	by(auto intro: preserves_NewThread)
    next
      fix x
      assume esT: "ts T = \<lfloor>x\<rfloor>"
      with redT tt' esT have "ts' T = \<lfloor>x\<rfloor>"
	by -(erule redT_ts_Some_inv)
      with es't' have "X = x" by auto
      moreover
      from esT esokQ have "P x m" by- (erule ts_okD, assumption)
      with qex have "P x m'" by -(rule preserves_other[OF red])
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma RedT_preserves:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; ts_ok P ts m \<rbrakk> \<Longrightarrow> ts_ok P ts' m'"
apply(erule RedT_lift_preserveD4)
by(fastsimp elim: redT_preserves)

end

interpretation lifting_wf_Const: lifting_wf ["r" "\<lambda>x m. k"]
by(unfold_locales)



locale lifting_inv = lifting_wf r Q +
  fixes P :: "'i \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
  assumes invariant_red: "\<lbrakk> ((x, m), ta, x', m') \<in> r; P i x m; Q x m \<rbrakk> \<Longrightarrow> P i x' m'"
  assumes invariant_NewThread: "\<lbrakk> ((x, m), ta, x', m') \<in> r; P i x m; Q x m; NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<exists>i''. P i'' x'' m'"
  assumes invariant_other: "\<lbrakk> ((x, m), ta, x', m') \<in> r; P i x m; Q x m; P i'' x'' m; Q x'' m \<rbrakk> \<Longrightarrow> P i'' x'' m'"
begin

lemma redT_invariant:
  assumes redT: "\<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>"
  and esinvP: "ts_inv P I ts m"
  and esokQ: "ts_ok Q ts m"
  shows "ts_inv P (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) ts' m'"
proof(rule ts_invI)
  fix T X
  assume es't': "ts' T = \<lfloor>X\<rfloor>"
  obtain las tas was where ta: "ta = (las, tas, was)" by (cases ta, auto)
  with redT obtain x x'
    where red: "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
    and est: "ts t = \<lfloor>x\<rfloor>"
    and lota: "lock_ok_las ls t las"
    and cctta: "thread_oks ts m' tas"
    and wst: "ws t = None"
    and ls': "ls' = redT_updLs ls t las"
    and es': "ts' = redT_updTs (ts(t \<mapsto> x')) tas"
    and ws': "ws' = redT_updWs ws t was"
    by(auto elim!: redT.cases)
  from est esinvP obtain i where Iti: "I t = \<lfloor>i\<rfloor>" and qiex: "P i x m"
    by(auto dest: ts_invD)
  from est esokQ Iti have rex: "Q x m" by(auto dest!: ts_okD)
  show "\<exists>i. upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>i\<rfloor> \<and> P i X m'"
  proof(cases "t = T")
    assume tT: "t = T"
    from qiex red rex have "P i x' m'"
      by -(rule invariant_red)
    moreover
    from tT est cctta Iti have "upd_invs I P tas t = \<lfloor>i\<rfloor>"
      by(auto intro: upd_invs_Some) 
    moreover from es't' es' tT
    have "redT_updTs (ts(T \<mapsto> x')) tas T = \<lfloor>X\<rfloor>"
      by(auto)
    hence "((redT_updTs ts tas)(T \<mapsto> x')) T = \<lfloor>X\<rfloor>"
      by(simp only: redT_updTs_upd[OF est cctta] tT[THEN sym])
    hence "X = x'" by(auto)
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
      fix x
      assume esT: "ts T = \<lfloor>x\<rfloor>"
      with redT tT have "ts' T = \<lfloor>x\<rfloor>" by -(erule redT_ts_Some_inv)
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
qed

lemma RedT_invariant:
  assumes RedT: "\<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>"
  and esinvQ: "ts_inv P I ts m"
  and esokR: "ts_ok Q ts m"
  shows "ts_inv P (upd_invs I P (\<down>map (thr_a \<circ> snd) ttas\<down>)) ts' m'"
using RedT esinvQ esokR
proof(induct rule: RedT_induct4)
  case refl thus ?case by(simp (no_asm))
next
  case (step LS TS M WS TTAS LS' TS' M' WS' T TA LS'' TS'' M'' WS'')
  note Red = `\<langle>LS, (TS, M), WS\<rangle> -\<triangleright>TTAS\<rightarrow>* \<langle>LS', (TS', M'), WS'\<rangle>`
  note IH = `\<lbrakk>ts_inv P I TS M; ts_ok Q TS M\<rbrakk> \<Longrightarrow> ts_inv P (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>)) TS' M'`
  note red = `\<langle>LS', (TS', M'), WS'\<rangle> -T\<triangleright>TA\<rightarrow> \<langle>LS'', (TS'', M''), WS''\<rangle>`
  note esinvQ = `ts_inv P I TS M`
  note esokR = `ts_ok Q TS M`
  have esinvQ': "ts_inv P (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>)) TS' M'"
    by(auto intro!: IH[OF esinvQ esokR] simp del: thr_a_def)
  have esokR': "ts_ok Q TS' M'"
    by(rule RedT_preserves[OF Red esokR])
  have "ts_inv P (upd_invs (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>)) P \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>) TS'' M''"
    by (rule redT_invariant[OF red esinvQ' esokR'])
  thus ?case
    by(simp add: comp_def)
qed

end


end
