(*  Title:      JinjaThreads/Framework/FWLiftingSem.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantic properties of lifted predicates} *}

theory FWLiftingSem imports FWSemantics FWLifting begin

context multithreaded_base begin

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
  shows "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; ts_inv_ok (thr s) I \<rbrakk> \<Longrightarrow> I \<subseteq>\<^sub>m upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
by(erule redT.cases, auto intro: ts_inv_ok_inv_ext_upd_invs)

lemma RedT_upd_inv_ext:
  fixes I :: "'t \<rightharpoonup> 'i"
  shows "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ts_inv_ok (thr s) I \<rbrakk>
         \<Longrightarrow> I \<subseteq>\<^sub>m upd_invs I P (\<down>map (thr_a \<circ> snd) ttas\<down>)"
proof(induct rule: RedT_induct)
  case refl thus ?case by simp
next
  case (step S TTAS S' T TA S'')
  hence "ts_inv_ok (thr S') (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>))"
    by -(rule RedT_preserves_ts_inv_ok)
  hence "upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>) \<subseteq>\<^sub>m upd_invs (upd_invs I P (\<down>map (thr_a \<circ> snd) TTAS\<down>)) P \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>" 
    using step by -(rule redT_upd_inv_ext)
  with step show ?case by(auto elim!: map_le_trans simp add: comp_def)
qed

end

locale lifting_wf = multithreaded _ r
  for r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) +
  fixes P :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
  assumes preserves_red: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P t x m \<rbrakk> \<Longrightarrow> P t x' m'"
  assumes preserves_NewThread: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P t x m; NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> P t'' x'' m'"
  assumes preserves_other: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P t x m; P t' x'' m \<rbrakk> \<Longrightarrow> P t' x'' m'"
begin

lemma redT_updTs_preserves:
  assumes esokQ: "ts_ok P ts m"
  and red: "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
  and "ts t = \<lfloor>(x, ln)\<rfloor>"
  and "thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "ts_ok P (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', ln'))) m'"
proof(rule ts_okI)
  fix T X LN
  assume XLN: "(redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', ln'))) T = \<lfloor>(X, LN)\<rfloor>"
  from esokQ `ts t = \<lfloor>(x, ln)\<rfloor>` have "P t x m" by(rule ts_okD)
  show "P T X m'"
  proof(cases "T = t")
    case True
    from red `P t x m` have "P t x' m'" by(rule preserves_red)
    with True XLN show ?thesis by simp
  next
    case False
    hence XLN: "redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>(X, LN)\<rfloor>" using XLN by simp
    show ?thesis
    proof(cases "ts T")
      case None
      with XLN `thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>` have "\<exists>m'. NewThread T X m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
        by(auto dest: redT_updTs_new_thread)
      with red have "NewThread T X m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by(auto dest: new_thread_memory)
      with red `P t x m` show "P T X m'" by(rule preserves_NewThread)
    next
      case (Some a)
      obtain X LN where [simp]: "a = (X, LN)" by (cases a, auto)
      from Some have esT: "ts T = \<lfloor>(X, LN)\<rfloor>" by simp
      hence "redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>(X, LN)\<rfloor>"
        using `thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>` by(auto intro: redT_updTs_Some)
      moreover from esokQ esT have "P T X m" by(rule ts_okD)
      with red `P t x m` have "P T X m'" by(rule preserves_other)
      ultimately show ?thesis using XLN by simp
    qed
  qed
qed

theorem redT_preserves:
  assumes redT: "s -t\<triangleright>ta\<rightarrow> s'"
  and esokQ: "ts_ok P (thr s) (shr s)"
  shows "ts_ok P (thr s') (shr s')"
using redT
proof(cases rule: redT_elims)
  case (normal x x' ta' m')
  with esokQ have "ts_ok P (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>))) m'"
    by(auto intro: redT_updTs_preserves)
  thus ?thesis using normal by simp
next
  case acquire thus ?thesis using esokQ
    by(auto intro!: ts_okI split: split_if_asm dest: ts_okD)
qed

theorem RedT_preserves:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
by(erule (1) RedT_lift_preserveD)(fastsimp elim: redT_preserves)

end

lemma lifting_wf_Const [intro!]: 
  assumes "multithreaded r"
  shows "lifting_wf r (\<lambda>t x m. k)"
proof -
  interpret multithreaded final r using assms .
  show ?thesis by(unfold_locales)
qed

locale lifting_inv = lifting_wf final r Q
  for final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and Q :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool" +
  fixes P :: "'i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
  assumes invariant_red: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P i t x m; Q t x m \<rbrakk> \<Longrightarrow> P i t x' m'"
  and invariant_NewThread: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P i t x m; Q t x m; NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> 
                            \<Longrightarrow> \<exists>i''. P i'' t'' x'' m'"
  and invariant_other: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P i t x m; Q t x m; P i'' t'' x'' m; Q t'' x'' m \<rbrakk> \<Longrightarrow> P i'' t'' x'' m'"
begin

lemma redT_updTs_invariant:
  assumes tsiP: "ts_inv P I ts m"
  and tsoQ: "ts_ok Q ts m"
  and red: "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
  and tao: "thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  and tst: "ts t = \<lfloor>(x, ln)\<rfloor>"
  shows "ts_inv P (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', ln'))) m'"
proof(rule ts_invI)
  fix T X LN
  assume XLN: "(redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', ln'))) T = \<lfloor>(X, LN)\<rfloor>"
  from tsiP tsoQ `ts t = \<lfloor>(x, ln)\<rfloor>` obtain i where "I t = \<lfloor>i\<rfloor>" "P i t x m" "Q t x m"
    by(auto dest: ts_okD ts_invD)
  show "\<exists>i. upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>i\<rfloor> \<and> P i T X m'"
  proof(cases "T = t")
    case True
    from red `P i t x m` `Q t x m` have "P i t x' m'" by(rule invariant_red)
    moreover from `I t = \<lfloor>i\<rfloor>` `ts t = \<lfloor>(x, ln)\<rfloor>` tao 
    have "upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>i\<rfloor>"
      by(simp add: upd_invs_Some)
    ultimately show ?thesis using True XLN by simp
  next
    case False
    show ?thesis
    proof(cases "ts T")
      case None
      with XLN tao False have "\<exists>m'. NewThread T X m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
        by(auto dest: redT_updTs_new_thread)
      with red have nt: "NewThread T X m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by(auto dest: new_thread_memory)
      with red `P i t x m` `Q t x m` have "\<exists>i''. P i'' T X m'" by(rule invariant_NewThread)
      hence "P (SOME i. P i T X m') T X m'" by(rule someI_ex)
      with nt tao show ?thesis by(auto intro: SOME_new_thread_upd_invs) 
    next
      case (Some a)
      obtain X' LN' where [simp]: "a = (X', LN')" by(cases a)
      with `ts T = \<lfloor>a\<rfloor>` have esT: "ts T = \<lfloor>(X', LN')\<rfloor>" by simp
      hence "redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>(X', LN')\<rfloor>"
        using `thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>` by(auto intro: redT_updTs_Some)
      moreover from esT tsiP tsoQ obtain i' where "I T = \<lfloor>i'\<rfloor>" "P i' T X' m" "Q T X' m"
        by(auto dest: ts_okD ts_invD)
      from red `P i t x m` `Q t x m` `P i' T X' m` `Q T X' m`
      have "P i' T X' m'" by(rule invariant_other)
      moreover from `I T = \<lfloor>i'\<rfloor>` esT tao have "upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>i'\<rfloor>"
        by(simp add: upd_invs_Some)
      ultimately show ?thesis using XLN False by simp
    qed
  qed
qed

theorem redT_invariant:
  assumes redT: "s -t\<triangleright>ta\<rightarrow> s'"
  and esinvP: "ts_inv P I (thr s) (shr s)"
  and esokQ: "ts_ok Q (thr s) (shr s)"
  shows "ts_inv P (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (thr s') (shr s')"
using redT
proof(cases rule: redT_elims)
  case acquire thus ?thesis using esinvP 
    by(auto intro!: ts_invI split: split_if_asm dest: ts_invD)
next
  case (normal x x' ta' m')
  with esokQ esinvP
  have "ts_ok Q (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>))) m'"
    and "ts_inv P (upd_invs I P \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>) (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>))) m'"
    by(auto intro: redT_updTs_preserves redT_updTs_invariant)
  thus ?thesis using normal by simp
qed

theorem RedT_invariant:
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
    using `S' -T\<triangleright>TA\<rightarrow> S''` by -(rule redT_invariant)
  thus ?case by(simp add: comp_def)
qed

end

end
