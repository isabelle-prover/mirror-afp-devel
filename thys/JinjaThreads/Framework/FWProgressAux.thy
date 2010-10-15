(*  Title:      JinjaThreads/Framework/FWProgressAux.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Auxiliary definitions for the progress theorem for the multithreaded semantics} *}

theory FWProgressAux imports FWSemantics begin

context multithreaded_base begin

definition must_sync :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>" [50, 0,0] 81) where
  "t \<turnstile> \<langle>x, m\<rangle> \<wrong> \<longleftrightarrow> (\<exists>ta x' m'. t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>)"

lemma must_syncI:
  "\<exists>ta x' m'. t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<Longrightarrow> t \<turnstile> \<langle>x, m\<rangle> \<wrong>"
by(fastsimp simp add: must_sync_def)

lemma must_syncE:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> \<wrong>; \<And>ta x' m'. t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto simp only: must_sync_def)

definition can_sync :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> ('l + 't) set \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>" [50,0,0,0] 81) where
  "t \<turnstile> \<langle>x, m\<rangle> LT \<wrong> \<equiv> \<exists>ta x' m'. t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> (LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>})"

lemma can_syncI:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} \<rbrakk> \<Longrightarrow> t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>"
by(cases ta)(fastsimp simp add: can_sync_def)

lemma can_syncE:
  assumes "t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>"
  obtains ta x' m'
  where "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>" "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
  using assms
by(clarsimp simp add: can_sync_def)

lemma must_sync_ex_can_sync:
  "t \<turnstile> \<langle>x, m\<rangle> \<wrong> \<Longrightarrow> \<exists>LT. t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>"
by(auto intro: can_syncI elim!: must_syncE)

lemma can_sync_must_sync:
  "t \<turnstile> \<langle>x, m\<rangle> LT \<wrong> \<Longrightarrow> t \<turnstile> \<langle>x, m\<rangle> \<wrong>"
by(auto intro: must_syncI elim!: can_syncE)

lemma must_sync_can_sync_conv:
  "t \<turnstile> \<langle>x, m\<rangle> \<wrong> \<longleftrightarrow> (\<exists>LT. t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>)"
by(auto intro: must_sync_ex_can_sync can_sync_must_sync)

end

text {* Well-formedness conditions for final *}

context final_thread begin

definition final_thread :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool" where
  "final_thread s t \<equiv> (case thr s t of None \<Rightarrow> False | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> final x \<and> ln = no_wait_locks \<and> wset s t = None)"

inductive not_final_thread :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool"
for s :: "('l,'t,'x,'m,'w) state" and t :: "'t" where
  not_final_thread_final: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> final x \<rbrakk> \<Longrightarrow> not_final_thread s t"
| not_final_thread_wait_locks: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ln \<noteq> no_wait_locks \<rbrakk> \<Longrightarrow> not_final_thread s t"
| not_final_thread_wait_set: "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> not_final_thread s t"

lemma final_threadI:
  "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; final x; wset s t = None \<rbrakk> \<Longrightarrow> final_thread s t"
by(simp add: final_thread_def)

lemma final_threadE:
  assumes "final_thread s t"
  obtains x where "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "final x" "wset s t = None"
using assms by(auto simp add: final_thread_def)

declare not_final_thread.cases [elim]

lemmas not_final_thread_cases = not_final_thread.cases [consumes 1, case_names final wait_locks wait_set]

lemma not_final_thread_cases2 [consumes 2, case_names final wait_locks wait_set]:
  "\<lbrakk> not_final_thread s t; thr s t = \<lfloor>(x, ln)\<rfloor>;
     \<not> final x \<Longrightarrow> thesis; ln \<noteq> no_wait_locks \<Longrightarrow> thesis; \<And>w. wset s t = \<lfloor>w\<rfloor> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
by(auto)

lemma not_final_thread_iff:
  "not_final_thread s t \<longleftrightarrow> (\<exists>x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<not> final x \<or> ln \<noteq> no_wait_locks \<or> (\<exists>w. wset s t = \<lfloor>w\<rfloor>)))"
by(auto intro: not_final_thread.intros)

lemma not_final_thread_conv:
  "not_final_thread s t \<longleftrightarrow> thr s t \<noteq> None \<and> \<not> final_thread s t"
by(auto simp add: final_thread_def intro: not_final_thread.intros)

lemma not_final_thread_existsE:
  assumes "not_final_thread s t"
  obtains x ln where "thr s t = \<lfloor>(x, ln)\<rfloor>"
using assms by blast

lemma not_final_thread_final_thread_conv:
  "thr s t \<noteq> None \<Longrightarrow> \<not> final_thread s t \<longleftrightarrow> not_final_thread s t"
by(simp add: not_final_thread_iff final_thread_def)

lemma may_join_cond_action_oks:
  assumes "\<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'"
  shows "cond_action_oks s t cas"
using assms
proof (induct cas)
  case Nil thus ?case by clarsimp
next
  case (Cons ca cas)
  note IH = `\<lbrakk> \<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t' \<rbrakk>
             \<Longrightarrow> cond_action_oks s t cas`
  note ass = `\<And>t'. Join t' \<in> set (ca # cas) \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'`
  hence "\<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'" by simp
  hence "cond_action_oks s t cas" by(rule IH)
  moreover have "cond_action_ok s t ca"
  proof(cases ca)
    case (Join t')
    with ass have "\<not> not_final_thread s t'" "t \<noteq> t'" by auto
    thus ?thesis using Join by(auto simp add: not_final_thread_iff)
  qed
  ultimately show ?case by simp
qed

end

locale final_thread_wf = multithreaded +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  assumes final_no_red [dest]: "\<lbrakk> final x; t \<turnstile> (x, m) -ta\<rightarrow> (x', m') \<rbrakk> \<Longrightarrow> False" begin

lemma final_no_redT: 
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<rbrakk> \<Longrightarrow> \<not> final x"
by(auto elim!: redT_elims dest: final_no_red)

lemma red_not_final_thread:
  "s -t\<triangleright>ta\<rightarrow> s' \<Longrightarrow> not_final_thread s t"
by(fastsimp elim: redT.cases intro: not_final_thread.intros)

lemma redT_preserves_final_thread:
  "\<lbrakk> s -t'\<triangleright>ta\<rightarrow> s'; final_thread s t \<rbrakk> \<Longrightarrow> final_thread s' t"
apply(erule redT.cases)
 apply(clarsimp simp add: final_thread_def)
apply(auto simp add: final_thread_def dest: redT_updTs_None redT_updTs_Some intro: redT_updWs_None_implies_None)
done

end

text {* This locale simply fixes a start state *}
locale multithreaded_start = multithreaded +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  fixes start_state :: "('l,'t,'x,'m,'w) state"
  assumes lock_thread_ok_start_state: "lock_thread_ok (locks start_state) (thr start_state)"
  and wset_thread_ok_start_state: "wset_thread_ok (wset start_state) (thr start_state)"
begin

lemma preserves_lock_thread_ok: 
  "start_state -\<triangleright>tta\<rightarrow>* s \<Longrightarrow> lock_thread_ok (locks s) (thr s)"
  by(erule RedT_preserves_lock_thread_ok[OF _ lock_thread_ok_start_state])

lemma preserves_wset_thread_ok: 
  "start_state -\<triangleright>tta\<rightarrow>* s \<Longrightarrow> wset_thread_ok (wset s) (thr s)"
  by(erule RedT_preserves_wset_thread_ok[OF _ wset_thread_ok_start_state])

lemma in_wait_SuspendD:
  assumes major: "start_state -\<triangleright>tta\<rightarrow>* s" "thr s t = \<lfloor>(x, ln)\<rfloor>" "wset s t = \<lfloor>w\<rfloor>"
  and start: "wset start_state t = None"
  shows
  "\<exists>s0 s1 tta0 tta1 x0 ta w' ln'.
    start_state -\<triangleright>tta0\<rightarrow>* s0 \<and> s0 -t\<triangleright>ta\<rightarrow> s1 \<and> s1 -\<triangleright>tta1\<rightarrow>* s \<and> 
    tta = tta0 @ (t, ta) # tta1 \<and>
    thr s0 t = \<lfloor>(x0, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x0, shr s0\<rangle> -ta\<rightarrow> \<langle>x, shr s1\<rangle> \<and> Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and>
    actions_ok s0 t ta \<and> thr s1 t = \<lfloor>(x, ln')\<rfloor>"
using major
proof(induct start_state tta s arbitrary: w ln rule: RedT_induct')
  case refl thus ?case using start by simp
next
  case (step ttas s' t' ta s'')
  show ?case
  proof(cases "wset s' t")
    case None
    with `thr s'' t = \<lfloor>(x, ln)\<rfloor>` `s' -t'\<triangleright>ta\<rightarrow> s''` `wset s'' t = \<lfloor>w\<rfloor>`
    obtain x0 m where m: "m = shr s''"
      and tt': "t = t'"
      and r: "t \<turnstile> \<langle>x0, shr s'\<rangle> -ta\<rightarrow> \<langle>x, m\<rangle>"
      and tst: "thr s' t = \<lfloor>(x0, no_wait_locks)\<rfloor>"
      and aok: "actions_ok s' t ta"
      and s': "redT_upd s' t ta x m s''"
      using redT_updWs_None_implies_None[where t=t and t'=t' and ws = "wset s'"]
      by(fastsimp elim!: redT.cases split: split_if_asm)
    from s' `wset s'' t = \<lfloor>w\<rfloor>` obtain ws'
      where "wset s'' = ws'"
      and red_Ws: "redT_updWs t (wset s') \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> ws'" "ws' t = \<lfloor>w\<rfloor>" by auto
    from redT_updWs_None_SomeD[OF red_Ws(1), OF red_Ws(2) `wset s' t = None`]
    obtain w' where "Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by auto
    thus ?thesis using `start_state -\<triangleright>ttas\<rightarrow>* s'` `s' -t'\<triangleright>ta\<rightarrow> s''` tst r aok
        `thr s'' t = \<lfloor>(x, ln)\<rfloor>` tt' m
      by(fastsimp intro: RedT_refl simp del: split_paired_Ex)
  next
    case (Some w')
    show ?thesis
    proof(cases "t = t'")
      case False
      with `redT s' (t', ta) s''` `thr s'' t = \<lfloor>(x, ln)\<rfloor>` `wset s'' t = \<lfloor>w\<rfloor>` 
      obtain w' where "redT_updTs (thr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>(x, ln)\<rfloor>"
        and "wset s' t = \<lfloor>w'\<rfloor>" "thread_oks (thr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
        by(fastsimp elim!: redT.cases dest: redT_updWs_Some_otherD[OF _ _ False] split: wait_set_status.split_asm)
      from `start_state -\<triangleright>ttas\<rightarrow>* s'` have "wset_thread_ok (wset s') (thr s')"
        by(rule preserves_wset_thread_ok)
      with `redT_updTs (thr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>(x, ln)\<rfloor>` `thread_oks (thr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>` `wset s' t = \<lfloor>w'\<rfloor>`
      have "thr s' t = \<lfloor>(x, ln)\<rfloor>"
        by(cases "thr s' t")(auto dest: wset_thread_okD redT_updTs_Some)
      from step.hyps(2)[OF this `wset s' t = \<lfloor>w'\<rfloor>`] `redT s' (t', ta) s''`
      show ?thesis unfolding RedT_def by(auto)(blast intro: rtrancl3p_step)
    next
      case True
      from `s' -t'\<triangleright>ta\<rightarrow> s''`
      show ?thesis
      proof(cases)
        case (redT_normal x0 X m)
        with `thr s'' t = \<lfloor>(x, ln)\<rfloor>` `wset s'' t = \<lfloor>w\<rfloor>` True
        have m: "m = shr s''" and [simp]: "X = x"
          and r: "t \<turnstile> \<langle>x0, shr s'\<rangle> -ta\<rightarrow> \<langle>x, m\<rangle>"
          and tst: "thr s' t = \<lfloor>(x0, no_wait_locks)\<rfloor>"
          and aok: "actions_ok s' t ta"
          and s': "redT_upd s' t ta x m s''"
          by(auto)
        from s' `wset s'' t = \<lfloor>w\<rfloor>` obtain ws' where "wset s'' = ws'"
          and red_Ws: "redT_updWs t (wset s') \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> ws'" "ws' t = \<lfloor>w\<rfloor>" by auto
        have "\<exists>w. Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence Suspend: "\<And>w. Suspend w \<notin> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by simp
          from redT_updWs_not_Suspend_Some[OF `redT_updWs t (wset s') \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> ws'`, OF `ws' t = \<lfloor>w\<rfloor>` Some this]
          show False using aok s' red_Ws Some
            by(auto simp add: wset_actions_ok_def split: split_if_asm dest: redT_updWs_Woken_Up_same_no_Notified_Interrupted[OF _ _ _ Suspend])
        qed
        then obtain w where Suspend: "Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" ..
        thus ?thesis using `start_state -\<triangleright>ttas\<rightarrow>* s'` `s' -t'\<triangleright>ta\<rightarrow> s''` tst r aok
          `thr s'' t = \<lfloor>(x, ln)\<rfloor>` True m
          by(fastsimp intro: RedT_refl simp del: split_paired_Ex)
      next
        case (redT_acquire X0 ln0 n)
        with `thr s'' t = \<lfloor>(x, ln)\<rfloor>` True
        have "thr s' t = \<lfloor>(x, ln0)\<rfloor>" by simp
        from step.hyps(2)[OF this Some] `redT s' (t', ta) s''`
        show ?thesis unfolding RedT_def
          by(auto)(blast intro: rtrancl3p_step)
      qed
    qed
  qed
qed

end

end