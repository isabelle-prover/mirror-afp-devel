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
  and "set cas \<inter> {Notified, Interrupted} = {}"
  shows "cond_action_oks s t cas"
using assms
proof (induct cas)
  case Nil thus ?case by clarsimp
next
  case (Cons ca cas)
  note IH = `\<lbrakk> \<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'; set cas \<inter> {Notified, Interrupted} = {} \<rbrakk>
             \<Longrightarrow> cond_action_oks s t cas`
  note ass = `\<And>t'. Join t' \<in> set (ca # cas) \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'`
  hence "\<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'" by simp
  moreover from `set (ca # cas) \<inter> {Notified, Interrupted} = {}`
  have "set cas \<inter> {Notified, Interrupted} = {}" by auto
  ultimately have "cond_action_oks s t cas" by(rule IH)
  moreover have "cond_action_ok s t ca" using `set (ca # cas) \<inter> {Notified, Interrupted} = {}`
  proof(cases ca)
    case (Join t')
    with ass have "\<not> not_final_thread s t'" "t \<noteq> t'" by auto
    thus ?thesis using Join by(auto simp add: not_final_thread_iff)
  qed auto
  ultimately show ?case by simp
qed

end

locale final_thread_wf = multithreaded +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
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
 apply(frule redTWs_no_wait_thr_other[where t'=t])
   apply fastsimp
  apply clarsimp
 apply(drule redTWs_no_wait_thr_unchanged[where t'=t])
apply(auto simp add: final_thread_def dest: redT_updTs_None redT_updTs_Some)
done

end

context multithreaded_base begin

inductive interrupted_mem_red :: 
  "('l, 't, 'x) thread_info \<Rightarrow> ('w, 't) wait_sets \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool"
for ts :: "('l, 't, 'x) thread_info" and ws :: "('w, 't) wait_sets" and m :: 'm and m' :: 'm
where
  "\<lbrakk> ts t = \<lfloor>(x, ln)\<rfloor>; ws t = \<lfloor>w\<rfloor>; t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; is_Interrupted_ta ta \<rbrakk>
  \<Longrightarrow> interrupted_mem_red ts ws m m'"

abbreviation interrupted_mem_reds ::
  "('l, 't, 'x) thread_info \<Rightarrow> ('w, 't) wait_sets \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool"
where "interrupted_mem_reds ts ws \<equiv> (interrupted_mem_red ts ws)^**"

lemma redTW_interrupted_mem_reds:
  "redTW t wa s obs s' \<Longrightarrow> interrupted_mem_reds (thr s) (wset s) (shr s) (shr s')"
by(fastsimp elim!: redTW.cases intro!: interrupted_mem_red.intros)

lemma interrupted_mem_red_mono_redTW:
  "\<lbrakk> interrupted_mem_red (thr s) (wset s) m m'; redTW t wa s' obs s; \<And>w. wa \<noteq> Suspend w \<rbrakk> 
  \<Longrightarrow> interrupted_mem_red (thr s') (wset s') m m'"
by(auto elim!: interrupted_mem_red.cases redTW.cases intro!: interrupted_mem_red.intros split: split_if_asm)

lemma interrupted_mem_reds_mono_redTW:
  assumes major: "interrupted_mem_reds (thr s) (wset s) m m'"
  and minor: "redTW t wa s' obs s" "\<And>w. wa \<noteq> Suspend w"
  shows "interrupted_mem_reds (thr s') (wset s') m m'"
using major
by induct(blast dest: interrupted_mem_red_mono_redTW[OF _ minor] intro: rtranclp.rtrancl_into_rtrancl)+

lemma interrupted_mem_reds_mono_redTWs:
  assumes minor1: "interrupted_mem_reds (thr s) (wset s) m m'" 
  and major: "redTWs t was s' obs s"
  and minor2: "\<And>w. Suspend w \<notin> set was"
  shows "interrupted_mem_reds (thr s') (wset s') m m'"
using major minor1 minor2
by induct(auto dest: interrupted_mem_reds_mono_redTW)

lemma redTWs_interrupted_mem_reds:
  assumes "redTWs t was s obs s'"
  and "\<And>w. Suspend w \<notin> set was"
  shows "interrupted_mem_reds (thr s) (wset s) (shr s) (shr s')"
using assms
apply(induct rule: redTWs_converse_induct)
 apply(rule rtranclp.rtrancl_refl)
apply(frule redTW_interrupted_mem_reds)
apply(drule (1) interrupted_mem_reds_mono_redTWs, simp)
apply(erule meta_impE)
apply simp
apply(blast intro: rtranclp_trans)
done

lemma interrupted_mem_red_thr_change:
  "\<lbrakk> interrupted_mem_red ts ws m m'; ts |` dom ws = ts' |` dom ws \<rbrakk> \<Longrightarrow> interrupted_mem_red ts' ws m m'"
by(fastsimp elim!: interrupted_mem_red.cases intro: interrupted_mem_red.intros simp add: restrict_map_def expand_fun_eq split: split_if_asm)

lemma interrupted_mem_reds_thr_change:
  assumes "interrupted_mem_reds ts ws m m'"
  and "ts |` dom ws = ts' |` dom ws"
  shows "interrupted_mem_reds ts' ws m m'"
using assms
by induct(blast intro: interrupted_mem_red_thr_change rtranclp.rtrancl_into_rtrancl)+

end

context multithreaded begin

lemma redTWs_interrupted_mem_reds_ta:
  assumes "redTWs t was s obs s'" and "r t' xm ta xm'" and was [simp]: "was = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
  shows "interrupted_mem_reds (thr s) (wset s) (shr s) (shr s')"
proof(cases "\<exists>w. Suspend w \<in> set was")
  case False
  hence "\<And>w. Suspend w \<notin> set was" by simp
  with `redTWs t was s obs s'` show ?thesis by(rule redTWs_interrupted_mem_reds)
next
  case True
  then obtain w where "Suspend w \<in> set was" by auto
  moreover from `r t' xm ta xm'` have "\<And>w. Suspend w \<notin> set (butlast \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>)" by(rule ta_Suspend_last)
  ultimately obtain was' where [simp]: "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = was' @ [Suspend w]" 
    and Suspend: "\<And>w. Suspend w \<notin> set was'" by(cases was rule: rev_cases) auto
  with `redTWs t was s obs s'` show ?thesis
    by(cases rule: redTWs_converseE)(auto elim!: redTW_cases dest: redTWs_interrupted_mem_reds)
qed

end

text {* This locale simply fixes a start state *}
locale multithreaded_start = multithreaded +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
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
  "\<exists>s0 s1 tta0 tta1 x0 m1 ta obs.
    start_state -\<triangleright>tta0\<rightarrow>* s0 \<and> s0 -t\<triangleright>observable_ta_of ta obs\<rightarrow> s1 \<and> s1 -\<triangleright>tta1\<rightarrow>* s \<and> 
    tta = tta0 @ (t, observable_ta_of ta obs) # tta1 \<and>
    thr s0 t = \<lfloor>(x0, no_wait_locks)\<rfloor> \<and> wset s0 t = None \<and> t \<turnstile> \<langle>x0, shr s0\<rangle> -ta\<rightarrow> \<langle>x, m1\<rangle> \<and> Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and>
    actions_ok s0 t ta \<and> thr s1 t = \<lfloor>(x, ln)\<rfloor> \<and> interrupted_mem_reds (thr s0) (wset s0) m1 (shr s1)"
using major
proof(induct start_state tta s rule: RedT_induct')
  case refl thus ?case using start by simp
next
  case (step ttas s' t' ta s'')
  show ?case
  proof(cases "t' = t")
    case True
    with `thr s'' t = \<lfloor>(x, ln)\<rfloor>` `s' -t'\<triangleright>ta\<rightarrow> s''` `wset s'' t = \<lfloor>w\<rfloor>`
    obtain x0 x1 ta' m obs where r: "t \<turnstile> \<langle>x0, shr s'\<rangle> -ta'\<rightarrow> \<langle>x1, m\<rangle>"
      and tst: "thr s' t = \<lfloor>(x0, no_wait_locks)\<rfloor>"
      and "wset s' t = None"
      and "actions_ok s' t ta"
      and ta [simp]: "ta = observable_ta_of ta' obs"
      and s': "redTWs t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_upd s' t ta x1 m) obs s''"
      by(auto elim!: redT.cases)
    have "\<exists>w. Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence "\<And>w. Suspend w \<notin> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" by simp
      from redTWs_ws_map_le[OF s' this] `wset s' t = None` `wset s'' t = \<lfloor>w\<rfloor>`
      show False by(auto dest: map_le_SomeD)
    qed
    then obtain w' where Suspend': "Suspend w' \<in> set \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>" by auto
    with ta_Suspend_last[OF r]
    obtain was where was: "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = was @ [Suspend w']"
      and Suspend': "\<And>w. Suspend w \<notin> set was" by(cases "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>" rule: rev_cases)(auto)
    moreover
    with s' `wset s'' t = \<lfloor>w\<rfloor>` have "w' = w"
      by (cases rule: redTWs_converseE)(auto elim!: redTW_cases)
    moreover
    from s' redTWs_thr_same_not_Suspend[OF _ Suspend', of t] `thr s'' t = \<lfloor>(x, ln)\<rfloor>` was `wset s' t = None`
    have "x1 = x" by(cases rule: redTWs_converseE)(fastsimp elim: redTW_cases)+
    moreover {
      from s' redTWs_interrupted_mem_reds[OF _ Suspend', of t "(redT_upd s' t ta x1 m)"]
      
      have "interrupted_mem_reds (redT_updTs (thr s') \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x1, redT_updLns (locks s') t (snd (the (thr s' t))) \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>))) (wset s') m (shr s'')"
        using was unfolding ta by(cases rule: redTWs_converseE)(auto elim: redTW_cases)
      moreover from `start_state -\<triangleright>ttas\<rightarrow>* s'` have "wset_thread_ok (wset s') (thr s')" by(rule preserves_wset_thread_ok)
      hence "(redT_updTs (thr s') \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x1, redT_updLns (locks s') t (snd (the (thr s' t))) \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>))) |` dom (wset s') = (thr s') |` dom (wset s')"
        using `actions_ok s' t ta`
        apply(auto simp add: restrict_map_def expand_fun_eq `wset s' t = None`)
        apply(case_tac "thr s' x")
        apply(auto dest: wset_thread_okD intro: redT_updTs_Some)
        done
      ultimately have "interrupted_mem_reds (thr s') (wset s') m (shr s'')" by(rule interrupted_mem_reds_thr_change) }
    ultimately show ?thesis
      using `start_state -\<triangleright>ttas\<rightarrow>* s'` `s' -t'\<triangleright>ta\<rightarrow> s''` tst `wset s' t = None` r `actions_ok s' t ta`
        `thr s'' t = \<lfloor>(x, ln)\<rfloor>`
      unfolding True ta `w' = w` by(auto intro: RedT_refl intro!: exI simp del: split_paired_Ex)
  next
    case False
    from `redT s' (t', ta) s''` `thr s'' t = \<lfloor>(x, ln)\<rfloor>` `wset s'' t = \<lfloor>w\<rfloor>` False
    have "redT_updTs (thr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>(x, ln)\<rfloor>" "wset s' t = \<lfloor>w\<rfloor>" "thread_oks (thr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
      by(auto elim!: redT.cases dest: redTWs_wait_other_thr_unchanged redTWs_wait_other_before)
    from `start_state -\<triangleright>ttas\<rightarrow>* s'` have "wset_thread_ok (wset s') (thr s')" by(rule preserves_wset_thread_ok)
    with `redT_updTs (thr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>(x, ln)\<rfloor>` `thread_oks (thr s') \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>` `wset s' t = \<lfloor>w\<rfloor>`
    have "thr s' t = \<lfloor>(x, ln)\<rfloor>"
      by(cases "thr s' t")(auto dest: wset_thread_okD redT_updTs_Some)
    from step.hyps(2)[OF this `wset s' t = \<lfloor>w\<rfloor>`] `redT s' (t', ta) s''`
    show ?thesis unfolding RedT_def by(auto)(blast intro: rtrancl3p_step)
  qed
qed

end


end