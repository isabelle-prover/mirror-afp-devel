(*  Title:      JinjaThreads/Framework/FWSemantics.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{The multithreaded semantics} *}

theory FWSemantics imports
  FWWellform
  FWLockingThread
  FWCondAction
begin

definition redT_upd :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> ('l,'t,'x,'m,'w) state"
 where 
  "redT_upd s t ta x' m' =
   (redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>,
    ((redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (x', redT_updLns (locks s) t (snd (the (thr s t))) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)), m'),
    wset s)"

declare redT_upd_def [simp]

definition redT_acq :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l \<Rightarrow>\<^isub>f nat) \<Rightarrow> ('l,'t,'x,'m,'w) state"
where
  "redT_acq s t ln = (acquire_all (locks s) t ln, ((thr s)(t \<mapsto> (fst (the (thr s t)), no_wait_locks)), shr s), wset s)"

declare redT_upd_def [simp]

context final_thread begin

inductive actions_ok :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action \<Rightarrow> bool"
  for s :: "('l,'t,'x,'m,'w) state" and t :: 't and ta :: "('l,'t,'x','m,'w,'o) thread_action"
  where
  "\<lbrakk> lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<rbrakk> \<Longrightarrow> actions_ok s t ta"

declare actions_ok.intros [intro!]
declare actions_ok.cases [elim!]

lemma actions_ok_iff [simp]:
  "actions_ok s t ta \<longleftrightarrow> lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
by(auto)

lemma actions_ok_upd_empty_inv:
  "thr s t = \<lfloor>xln\<rfloor> \<Longrightarrow> actions_ok (redT_upd s t \<epsilon> x' (shr s)) t ta = actions_ok s t ta"
by(auto simp add: redT_updLns_def redT_updLs_def cond_action_oks_upd thread_oks_upd)

inductive actions_ok' :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action \<Rightarrow> bool" where
  "\<lbrakk> lock_ok_las' (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; cond_action_oks' s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<rbrakk> \<Longrightarrow> actions_ok' s t ta"

declare actions_ok'.intros [intro!]
declare actions_ok'.cases [elim!]

lemma actions_ok'_iff:
  "actions_ok' s t ta \<longleftrightarrow> lock_ok_las' (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> cond_action_oks' s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
by auto

lemma actions_ok'_ta_upd_obs:
  "actions_ok' s t (ta\<lbrace>\<^bsub>o\<^esub> obs\<rbrace>) \<longleftrightarrow> actions_ok' s t ta"
by(cases ta)(auto simp add: actions_ok'_iff lock_ok_las'_def ta_upd_simps)

inductive actions_subset :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action \<Rightarrow> bool"
where
 "\<lbrakk> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<rbrakk> 
  \<Longrightarrow> actions_subset ta' ta"

declare actions_subset.intros [intro!]
declare actions_subset.cases [elim!]

lemma actions_subset_iff:
  "actions_subset ta' ta \<longleftrightarrow> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
                             collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
by auto

lemma actions_subset_refl [intro]:
  "actions_subset ta ta"
by(auto intro: actions_subset.intros collect_locks'_subset_collect_locks del: subsetI)

lemma actions_ok'_empty: "actions_ok' s t \<epsilon>"
by(simp add: actions_ok'_iff lock_ok_las'_def)

lemma actions_ok'_convert_extTA:
  "actions_ok' s t (convert_extTA f ta) = actions_ok' s t ta"
by(auto simp add: actions_ok'_iff)

definition mfinal :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where "mfinal s \<longleftrightarrow> (\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<longrightarrow> final x \<and> ln = no_wait_locks \<and> wset s t = None)"

lemma mfinalI:
  "(\<And>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> final x \<and> ln = no_wait_locks \<and> wset s t = None) \<Longrightarrow> mfinal s"
unfolding mfinal_def by blast

lemma mfinalD:
  assumes "mfinal s" "thr s t = \<lfloor>(x, ln)\<rfloor>"
  shows "final x" "ln = no_wait_locks" "wset s t = None"
using assms unfolding mfinal_def by blast+

lemma mfinalE:
  assumes "mfinal s" "thr s t = \<lfloor>(x, ln)\<rfloor>"
  obtains "final x" "ln = no_wait_locks" "wset s t = None"
using mfinalD[OF assms] by(rule that)

end


locale multithreaded_base = final_thread +
  constrains final :: "'x \<Rightarrow> bool" 
  fixes r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80)

sublocale multithreaded_base < trsys "r t" for t
.

context multithreaded_base begin

abbreviation
  r_syntax :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> ('l,'t,'x,'m,'w,'o list) thread_action \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool" ("_ \<turnstile> \<langle>_, _\<rangle> -_\<rightarrow> \<langle>_, _\<rangle>" [50,0,0,0,0,0] 80)
where
  "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<equiv> t \<turnstile> (x, m) -ta\<rightarrow> (x', m')"

inductive redTW :: "'t \<Rightarrow> ('t,'w) wait_set_action \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'o) observable list \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
for t :: 't
where
  redTW_Suspend:
  "\<lbrakk> s' = (locks s, (thr s, shr s), (wset s)(t \<mapsto> w)) \<rbrakk>
  \<Longrightarrow> redTW t (Suspend w) s [] s'"

| redTW_NotifyNone:
  "\<lbrakk> \<And>t. wset s t \<noteq> \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> redTW t (Notify w) s [] s"

| redTW_NotifySome:
  "\<lbrakk> wset s t' = \<lfloor>w\<rfloor>; \<And>x ln. thr s t' = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> t' \<turnstile> \<langle>x, shr s\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified \<rbrace>\<rightarrow> \<langle>x', shr s\<rangle>;
     s' = (locks s, ((thr s)(t' := Option.map (\<lambda>(x, ln). (x', ln)) (thr s t')), shr s), (wset s)(t' := None)) \<rbrakk>
  \<Longrightarrow> redTW t (Notify w) s [] s'"

| redTW_NotifyAll:
  "\<lbrakk> \<And>t' x ln. \<lbrakk> wset s t' = \<lfloor>w\<rfloor>; thr s t' = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> t' \<turnstile> \<langle>x, shr s\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified \<rbrace>\<rightarrow> \<langle>x' t', shr s\<rangle>;
     s' = (locks s, ((\<lambda>t'. if (wset s t' = \<lfloor>w\<rfloor>) then (Option.map (\<lambda>(x, ln). (x' t', ln)) (thr s t')) else thr s t'), shr s), 
           (\<lambda>t'. if wset s t' = \<lfloor>w\<rfloor> then None else wset s t')) \<rbrakk>
  \<Longrightarrow> redTW t (NotifyAll w) s [] s'"

| redTW_InterruptNone:
  "\<lbrakk> wset s t' = None \<rbrakk> \<Longrightarrow> redTW t (Interrupt t') s [] s"

| redTW_InterruptWait:
  "\<lbrakk> wset s t' = \<lfloor>w\<rfloor>; case (thr s t') of None \<Rightarrow> m' = shr s \<and> ta = \<epsilon>\<lbrace>\<^bsub>c\<^esub> Interrupted \<rbrace> | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> t' \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>;
     is_Interrupted_ta ta;
     s' = (locks s, ((thr s)(t' := Option.map (\<lambda>(x, ln). (x', ln)) (thr s t')), m'), (wset s)(t' := None)) \<rbrakk>
  \<Longrightarrow> redTW t (Interrupt t') s (observable_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) s'"

inductive_cases redTW_cases:
  "redTW t (Suspend w) s obs s'"
  "redTW t (Notify w) s obs s'"
  "redTW t (NotifyAll w) s obs s'"
  "redTW t (Interrupt t') s obs s'"

inductive redTWs :: "'t \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'o) observable list \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
for t :: 't
where
  Nil [iff]: "redTWs t [] s [] s"
| Cons: "\<lbrakk> redTW t ta s obs s'; redTWs t tas s' obs' s'' \<rbrakk> \<Longrightarrow> redTWs t (ta # tas) s (obs @ obs') s''"

inductive_cases redTWs_cases:
  "redTWs t [] s obs s'"
  "redTWs t (ta # tas) s obs s'"

lemma redTWs_trans [trans]:
  assumes "redTWs t tas s obs s'" "redTWs t tas' s' obs' s''"
  shows "redTWs t (tas @ tas') s (obs @ obs') s''"
using assms
by(induct arbitrary: tas' obs')(auto intro: redTWs.Cons)

lemma redTWs_Nil_conv [simp]:
  "redTWs t [] s obs s' \<longleftrightarrow> s' = s \<and> obs = []"
by(auto elim: redTWs_cases)

lemma redTWs_singleton_conv [simp]:
  "redTWs t [ta] = redTW t ta"
apply(rule ext)+
apply(auto elim!: redTWs_cases)
apply(drule redTWs.Cons[OF _ redTWs.Nil], simp)
done

lemma redTWs_snocI:
  assumes "redTWs t tas s obs s'" "redTW t ta s' obs' s''"
  shows "redTWs t (tas @ [ta]) s (obs @ obs') s''"
using assms by(auto intro: redTWs_trans)

lemma redTWs_snocD:
  assumes "redTWs t (tas @ [ta]) s obs s''"
  shows "\<exists>s' obs' obs''. obs = obs' @ obs'' \<and> redTWs t tas s obs' s' \<and> redTW t ta s' obs'' s''"
using assms
apply(induct tas arbitrary: s obs)
 apply simp
apply simp
apply(erule redTWs_cases)
apply clarify
apply(erule meta_allE)+
apply(erule (1) meta_impE)
apply clarify
apply(rule exI)+
apply(rule conjI)
 prefer 2
 apply(rule conjI)
  apply(erule (1) redTWs.Cons)
 apply assumption
apply simp
done

lemma redTWs_converse_induct [consumes 1, case_names Nil snoc]:
  assumes major: "redTWs t tas s obs s'"
  and Nil: "\<And>s. P [] s [] s"
  and snoc: "\<And>tas ta obs obs' s s' s''. \<lbrakk> redTWs t tas s obs s'; P tas s obs s'; redTW t ta s' obs' s'' \<rbrakk> \<Longrightarrow> P (tas @ [ta]) s (obs @ obs') s''"
  shows "P tas s obs s'"
using major
apply(induct tas arbitrary: s' obs rule: rev_induct)
 apply(blast elim: redTWs_cases intro: Nil)
apply(blast dest: redTWs_snocD intro: snoc)
done

lemma redTWs_converseE [consumes 1, case_names Nil snoc]:
  assumes "redTWs t tas s obs s'"
  obtains
    (Nil) "tas = []" "obs = []"
  | (snoc) ta tas' obs' obs'' s''
      where "tas = tas' @ [ta]" "obs = obs' @ obs''"
      and "redTWs t tas' s obs' s''" "redTW t ta s'' obs'' s'"
apply(atomize_elim)
using assms 
apply(induct rule: redTWs_converse_induct)
 apply simp
apply auto
apply(intro exI conjI)
  prefer 2
  apply(erule (1) redTWs_snocI)
 prefer 2
 apply assumption
apply simp
done

lemma redTW_locks_unchanged:
  "redTW t wa s obs s' \<Longrightarrow> locks s' = locks s"
by(auto elim: redTW.cases)

lemma redTWs_locks_unchanged:
  assumes "redTWs t was s obs s'"
  shows "locks s' = locks s"
using assms
by(induct)(auto dest: redTW_locks_unchanged)

lemma redTW_thr_None:
  "redTW t wa s obs s' \<Longrightarrow> thr s' t' = None \<longleftrightarrow> thr s t' = None"
by(auto elim!: redTW.cases split: split_if_asm)

lemma redTWs_thr_None:
  assumes "redTWs t wa s obs s'" 
  shows "thr s' t' = None \<longleftrightarrow> thr s t' = None"
using assms
by induct(auto dest!: redTW_thr_None)

lemma redTW_no_wait_thr_other:
  "\<lbrakk> redTW t wa s obs s'; t \<noteq> t'; wset s t' = None \<rbrakk> \<Longrightarrow> wset s' t' = None"
by(auto elim!: redTW.cases)

lemma redTWs_no_wait_thr_other:
  assumes "redTWs t was s obs s'" "t \<noteq> t'" "wset s t' = None"
  shows "wset s' t' = None"
using assms
by induct(auto dest: redTW_no_wait_thr_other)

lemma redTW_no_wait_thr_unchanged:
  "\<lbrakk> redTW t wa s obs s'; wset s t' = None \<rbrakk> \<Longrightarrow> thr s' t' = thr s t'"
by(auto elim!: redTW.cases)

lemma redTWs_no_wait_thr_unchanged:
  assumes "redTWs t was s obs s'" "wset s t' = None" "t' \<noteq> t"
  shows "thr s' t' = thr s t'"
using assms
by(induct)(fastsimp dest: redTW_no_wait_thr_unchanged redTW_no_wait_thr_other)+

lemma redTW_preserves_lock_thread_ok:
  "redTW t wa s obs s' \<Longrightarrow> lock_thread_ok (locks s') (thr s') \<longleftrightarrow> lock_thread_ok (locks s) (thr s)"
apply(rule iffI)
 apply(rule lock_thread_okI)
 apply(frule redTW_locks_unchanged)
 apply simp
 apply(erule (1) lock_thread_ok_has_lockE)
 apply(drule_tac t'=ta in redTW_thr_None)
 apply simp
apply(rule lock_thread_okI)
apply(frule redTW_locks_unchanged)
apply simp
apply(erule (1) lock_thread_ok_has_lockE)
apply(drule_tac t'=ta in redTW_thr_None)
apply simp
done

lemma redTWs_preserves_lock_thread_ok:
  assumes "redTWs t was s obs s'"
  shows "lock_thread_ok (locks s') (thr s') \<longleftrightarrow> lock_thread_ok (locks s) (thr s)"
using assms
by induct(simp_all add: redTW_preserves_lock_thread_ok)

lemma redTW_preserves_wset_thread_ok:
  "\<lbrakk> redTW t wa s obs s'; wset_thread_ok (wset s) (thr s); thr s t = \<lfloor>xln\<rfloor> \<rbrakk> \<Longrightarrow> wset_thread_ok (wset s') (thr s')"
apply(rule wset_thread_okI)
apply(erule redTW.cases)
apply(auto dest: wset_thread_okD)
done

lemma redTWs_preserves_wset_thread_ok:
  assumes "redTWs t was s obs s'" "wset_thread_ok (wset s) (thr s)" "thr s t = \<lfloor>xln\<rfloor>" 
  shows "wset_thread_ok (wset s') (thr s')"
using assms
apply(induct arbitrary: xln)
 apply simp
apply(frule redTW_thr_None[where t'=t])
apply(auto dest: redTW_preserves_wset_thread_ok)
done

lemma redTW_ws_map_le:
  "\<lbrakk> redTW t wa s obs s'; \<And>w. wa \<noteq> Suspend w \<rbrakk> \<Longrightarrow> wset s' \<subseteq>\<^sub>m wset s"
by(auto elim!: redTW.cases split: split_if_asm simp add: map_le_def)

lemma redTWs_ws_map_le:
  assumes "redTWs t was s obs s'"
  and "\<And>w. Suspend w \<notin> set was"
  shows "wset s' \<subseteq>\<^sub>m wset s"
using assms
by(induct)(auto dest!: redTW_ws_map_le intro: map_le_trans)

lemma redTWs_thr_same_not_Suspend:
  assumes "redTWs t was s obs s'"
  and "\<And>w. Suspend w \<notin> set was"
  and "wset s t = None"
  shows "thr s' t = thr s t"
using assms
apply(induct rule: redTWs_converse_induct)
apply(force dest!: redTWs_ws_map_le elim: redTW.cases simp add: map_le_def)+
done

lemma redTW_wait_other_before:
  "\<lbrakk> redTW t wa s obs s'; wset s' t' = \<lfloor>w\<rfloor>; t \<noteq> t' \<rbrakk> \<Longrightarrow> wset s t' = \<lfloor>w\<rfloor>"
by(auto elim!: redTW.cases split: split_if_asm)

lemma redTWs_wait_other_before:
  assumes "redTWs t wa s obs s'" "wset s' t' = \<lfloor>w\<rfloor>" "t \<noteq> t'"
  shows "wset s t' = \<lfloor>w\<rfloor>"
using assms by induct(auto dest: redTW_wait_other_before)

lemma redTW_wait_other_thr_unchanged:
  "\<lbrakk> redTW t wa s obs s'; wset s' t' = \<lfloor>w\<rfloor>; t \<noteq> t' \<rbrakk> \<Longrightarrow> thr s' t' = thr s t'"
by(auto elim!: redTW.cases split: split_if_asm)

lemma redTWs_wait_other_thr_unchanged:
  assumes "redTWs t wa s obs s'" "wset s' t' = \<lfloor>w\<rfloor>" "t \<noteq> t'"
  shows "thr s' t' = thr s t'"
using assms
by(induct rule: redTWs_converse_induct)(fastsimp dest: redTW_wait_other_thr_unchanged redTW_wait_other_before)+

lemma redTW_ls_ts_change: -- "not needed"
  assumes redTW: "redTW t wa (ls, (ts, m), ws) obs (ls', (ts', m'), ws')"
  and ts''ts: "ts'' |` (dom ws) = ts |` (dom ws)"
  shows "\<exists>ts'''. redTW t wa (ls'', (ts'', m), ws) obs (ls'', (ts''', m'), ws') \<and> ts''' |` dom ws = ts' |` dom ws"
using redTW
proof cases
  case redTW_Suspend thus ?thesis using ts''ts by(fastsimp intro: redTW.intros)
next
  case redTW_NotifyNone thus ?thesis using ts''ts by(fastsimp intro: redTW.intros)
next
  case (redTW_NotifySome t' w x')
  hence eqs [simp]: "wa = Notify w" "ls' = ls" "ts' = ts(t' := Option.map (\<lambda>(x, ln). (x', ln)) (ts t'))"
    "m' = m" "ws' = ws(t' := None)" "obs = []"
    and red: "\<And>x ln. ts t' = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> t' \<turnstile> \<langle>x, m\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> \<langle>x', m\<rangle>" 
    and wst': "ws t' = \<lfloor>w\<rfloor>" by auto
  let ?ts''' = "ts''(t' := Option.map (\<lambda>(x, ln). (x', ln)) (ts'' t'))"
  from ts''ts wst' have "ts'' t' = ts t'" by(auto simp add: restrict_map_def expand_fun_eq split: split_if_asm)
  hence "\<And>x ln. ts'' t' = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> t' \<turnstile> \<langle>x, m\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> \<langle>x', m\<rangle>"
    by(auto dest: red)
  with wst' have "redTW t wa (ls'', (ts'', m), ws) obs (ls'', (?ts''', m'), ws')"
    by(auto intro!: redTW.redTW_NotifySome)
  moreover from `ts'' t' = ts t'`
  have "?ts''' |` dom ws = ts' |` dom ws" using wst' ts''ts
    by(simp)(auto simp add: restrict_map_def expand_fun_eq)
  ultimately show ?thesis by blast
next
  case (redTW_NotifyAll w x')
  hence eqs [simp]: "wa = NotifyAll w" "ls' = ls" "m' = m" "obs = []"
    and ts': "ts' = (\<lambda>t'. if ws t' = \<lfloor>w\<rfloor> then Option.map (\<lambda>(x, ln). (x' t', ln)) (ts t') else ts t')"
    and red: "\<And>t' x ln. \<lbrakk> ws t' = \<lfloor>w\<rfloor>; ts t' = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> t' \<turnstile> \<langle>x, m\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> \<langle>x' t', m\<rangle>"
    and ws': "ws' = (\<lambda>t'. if ws t' = \<lfloor>w\<rfloor> then None else ws t')"
    by(auto cong: if_cong)
  let ?ts''' = "\<lambda>t'. if ws t' = \<lfloor>w\<rfloor> then Option.map (\<lambda>(x, ln). (x' t', ln)) (ts'' t') else ts'' t'"
  { fix t' x ln
    assume "ws t' = \<lfloor>w\<rfloor>" "ts'' t' = \<lfloor>(x, ln)\<rfloor>"
    with ts''ts have "ts t' = \<lfloor>(x, ln)\<rfloor>" by(auto simp add: restrict_map_def expand_fun_eq split: split_if_asm)
    with `ws t' = \<lfloor>w\<rfloor>` have "t' \<turnstile> \<langle>x, m\<rangle> -\<epsilon>\<lbrace>\<^bsub>c\<^esub> Notified\<rbrace>\<rightarrow> \<langle>x' t', m\<rangle>" by(rule red) }
  hence "redTW t wa (ls'', (ts'', m), ws) obs (ls'', (?ts''', m'), ws')" unfolding ws' 
    by(auto intro!: redTW.redTW_NotifyAll[where x'=x'] cong: if_cong)
  moreover from ts''ts have "?ts''' |` dom ws = ts' |` dom ws" unfolding ts'
    by(auto simp add: expand_fun_eq restrict_map_def split: split_if_asm)
  ultimately show ?thesis by blast
next
  case redTW_InterruptNone thus ?thesis using ts''ts by(fastsimp intro: redTW.intros)
next
  case (redTW_InterruptWait t' w M ta x')
  hence [simp]: "wa = Interrupt t'" "ls' = ls" "ts' = ts(t' := Option.map (\<lambda>(x, ln). (x', ln)) (ts t'))"
    "m' = M" "ws' = ws(t' := None)" "obs = observable_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and red: "case ts t' of None \<Rightarrow> M = m \<and> ta = \<epsilon>\<lbrace>\<^bsub>c\<^esub> Interrupted \<rbrace> | Some (x, ln) \<Rightarrow> t' \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', M\<rangle>"
    and wst': "ws t' = \<lfloor>w\<rfloor>" 
    and ta: "is_Interrupted_ta ta" by auto
  let ?ts''' = "ts''(t' := Option.map (\<lambda>(x, ln). (x', ln)) (ts'' t'))"
  from ts''ts wst' have "ts'' t' = ts t'" by(auto simp add: restrict_map_def expand_fun_eq split: split_if_asm)
  with red have "case ts'' t' of None \<Rightarrow> M = m \<and> ta = \<epsilon>\<lbrace>\<^bsub>c\<^esub> Interrupted \<rbrace> | Some (x, ln) \<Rightarrow> t' \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', M\<rangle>" by simp
  with wst' ta have "redTW t wa (ls'', (ts'', m), ws) obs (ls'', (?ts''', m'), ws')"
    using redTW.redTW_InterruptWait[of "(ls'', (ts'', m), ws)" t' w m' ta x' "(ls'', (?ts''', m'), ws')" t]
    by auto
  moreover from `ts'' t' = ts t'`
  have "?ts''' |` dom ws = ts' |` dom ws" using wst' ts''ts
    by(simp)(auto simp add: restrict_map_def expand_fun_eq)
  ultimately show ?thesis by blast
qed

inductive
  redT :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<times> ('l,'t,'x,'m,'w,('l,'o) observable list) thread_action \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool" and
  redT_syntax1 :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,('l,'o) observable list) thread_action \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool" ("_ -_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)
where
  "s -t\<triangleright>ta\<rightarrow> s' \<equiv> redT s (t, ta) s'"

|  redT_normal:
  "\<lbrakk> t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>;
     thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; wset s t = None;
     actions_ok s t ta;
     redTWs t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_upd s t ta x' m') obs s' \<rbrakk>
  \<Longrightarrow> s -t\<triangleright>observable_ta_of ta obs\<rightarrow> s'"

| redT_acquire:
  "\<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = None;
     may_acquire_all (locks s) t ln; ln\<^sub>f n > 0;
     s' = (acquire_all (locks s) t ln, (thr s(t \<mapsto> (x, no_wait_locks)), shr s), wset s) \<rbrakk>
  \<Longrightarrow> s -t\<triangleright>((\<lambda>\<^isup>f []), [], [], [], [ReacquireLocks ln])\<rightarrow> s'"

abbreviation
  redT_syntax2 :: "('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets
                   \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,('l,'o) observable list) thread_action
                   \<Rightarrow> ('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool"
                  ("\<langle>_, _, _\<rangle> -_\<triangleright>_\<rightarrow> \<langle>_, _, _\<rangle>" [0,0,0,0,0,0,0,0] 80)
where
  "\<langle>ls, tsm, ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', tsm', ws'\<rangle> \<equiv> (ls, tsm, ws) -t\<triangleright>ta\<rightarrow> (ls', tsm', ws')"

lemma redT_elims [consumes 1, case_names normal acquire]:
  assumes red: "s -t\<triangleright>ta\<rightarrow> s'"
  and normal: "\<And>x x' ta' m' obs. \<lbrakk> t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>; ta = observable_ta_of ta' obs; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
                        lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; wset s t = None;
                        cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>;
                        locks s' = redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>;
                        redTWs t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>, ((redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)), m'), wset s) obs s' \<rbrakk> \<Longrightarrow> thesis"
  and acquire: "\<And>x ln n. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ta = (\<lambda>\<^isup>f [], [], [], [], [ReacquireLocks ln]);
                           wset s t = None; may_acquire_all (locks s) t ln; ln\<^sub>f n > 0;
                           locks s' = acquire_all (locks s) t ln;
                           thr s' = thr s(t \<mapsto> (x, no_wait_locks));
                           wset s' = wset s; shr s' = shr s \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
using red
apply -
apply(erule redT.cases)
 apply(rule normal)
 apply(fastsimp dest: redTWs_locks_unchanged)+
apply(rule acquire, fastsimp+)
done

definition
  RedT :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> ('l,'t,'x,'m,'w,('l,'o) observable list) thread_action) list \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
          ("_ -\<triangleright>_\<rightarrow>* _" [50,0,50] 80)
where
  "RedT \<equiv> rtrancl3p redT"

abbreviation
  RedT_syntax :: "('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets
                  \<Rightarrow> ('t \<times> ('l,'t,'x,'m,'w,('l,'o) observable list) thread_action) list 
                  \<Rightarrow> ('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool"
                 ("\<langle>_, _, _\<rangle> -\<triangleright>_\<rightarrow>* \<langle>_, _, _\<rangle>" [0,0,0,0,0,0,0] 80)
where
  "\<langle>ls, tsm, ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', tsm', ws'\<rangle> \<equiv> (ls, tsm, ws) -\<triangleright>ttas\<rightarrow>* (ls', tsm', ws')"

lemma RedTI:
  "rtrancl3p redT s ttas s' \<Longrightarrow> RedT s ttas s'"
by(simp add: RedT_def)

lemma RedTE:
  "\<lbrakk> RedT s ttas s'; rtrancl3p redT s ttas s' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: RedT_def)

lemma RedTD:
  "RedT s ttas s' \<Longrightarrow> rtrancl3p redT s ttas s'"
by(simp add: RedT_def)

lemma RedT_induct [consumes 1, case_names refl step]:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s';
     \<And>s. P s [] s;
     \<And>s ttas s' t ta s''. \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; P s ttas s'; s' -t\<triangleright>ta\<rightarrow> s'' \<rbrakk> \<Longrightarrow> P s (ttas @ [(t, ta)]) s''\<rbrakk>
  \<Longrightarrow> P s ttas s'"
unfolding RedT_def
by(erule rtrancl3p.induct) auto

lemma RedT_induct4 [consumes 1, case_names refl step]:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>;
     \<And>ls ts m ws. P ls ts m ws [] ls ts m ws;
     \<And>ls ts m ws ttas ls' ts' m' ws' t ta ls'' ts'' m'' ws''.
       \<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; 
         P ls ts m ws ttas ls' ts' m' ws';
         \<langle>ls', (ts', m'), ws'\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls'', (ts'', m''), ws''\<rangle> \<rbrakk> 
       \<Longrightarrow> P ls ts m ws (ttas @ [(t, ta)]) ls'' ts'' m'' ws'' \<rbrakk>
  \<Longrightarrow> P ls ts m ws ttas ls' ts' m' ws'"
unfolding RedT_def
by(erule rtrancl3p_induct4')(auto)

lemma RedT_induct' [consumes 1, case_names refl step]:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s';
     P s [] s;
     \<And>ttas s' t ta s''. \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; P s ttas s'; s' -t\<triangleright>ta\<rightarrow> s'' \<rbrakk> \<Longrightarrow> P s (ttas @ [(t, ta)]) s''\<rbrakk>
  \<Longrightarrow> P s ttas s'"
  unfolding RedT_def
apply(erule rtrancl3p_induct', blast)
apply(case_tac b, blast)
done

lemma RedT_lift_preserveD:
  assumes Red: "s -\<triangleright>ttas\<rightarrow>* s'"
  and P: "P s"
  and preserve: "\<And>s t tas s'. \<lbrakk> s -t\<triangleright>tas\<rightarrow> s'; P s \<rbrakk> \<Longrightarrow> P s'"
  shows "P s'"
  using Red P
  by(induct rule: RedT_induct)(auto intro: preserve)

lemma RedT_lift_preserveD4:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; 
     P ls ts m ws;
     \<And>ls ts m ws t ta ls' ts' m' ws'. \<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; P ls ts m ws \<rbrakk> \<Longrightarrow> P ls' ts' m' ws' \<rbrakk>
  \<Longrightarrow> P ls' ts' m' ws'"
by(drule RedT_lift_preserveD[where P="(\<lambda>(ls, (ts, m), ws). P ls ts m ws)"])(auto)

lemma RedT_refl [intro, simp]:
  "s -\<triangleright>[]\<rightarrow>* s"
by(rule RedTI)(rule rtrancl3p_refl)

lemma redT_has_locks_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t' \<rbrakk> \<Longrightarrow>
  has_locks (ls\<^sub>f l) t' = has_locks (ls'\<^sub>f l) t'"
by(auto elim!: redT.cases intro: redT_updLs_has_locks[THEN sym, simplified] may_acquire_all_has_locks_acquire_locks[symmetric] dest!: redTWs_locks_unchanged)

lemma redT_has_lock_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t' \<rbrakk>
  \<Longrightarrow> has_lock (ls'\<^sub>f l) t' = has_lock (ls\<^sub>f l) t'"
by(auto simp add: redT_has_locks_inv)

lemma redT_ts_Some_inv_no_wait:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; t \<noteq> t'; ts t' = \<lfloor>x\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> ts' t' = \<lfloor>x\<rfloor>"
by(fastsimp elim!: redT.cases simp: redT_updTs_upd[THEN sym] intro: redT_updTs_Some dest: redTWs_no_wait_thr_unchanged[where t'=t'])

lemma redT_thread_not_disappear:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; ts' t' = None\<rbrakk> \<Longrightarrow> ts t' = None"
apply(cases "t \<noteq> t'")
 apply(erule redT_elims)
  apply(clarsimp)
  apply(drule redTWs_thr_None[where t'=t'])
  apply clarsimp
  apply(erule redT_updTs_None)
 apply(clarsimp)
apply(auto elim!: redT_elims simp add: redT_updTs_upd[THEN sym] dest: redTWs_thr_None[where t'=t'])
done

lemma RedT_thread_not_disappear:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>; ts' t' = None\<rbrakk> \<Longrightarrow> ts t' = None"
apply(erule contrapos_pp[where Q="ts' t' = None"])
apply(drule RedT_lift_preserveD4)
 apply(assumption)
apply(erule_tac Q="tsa t' = None" in contrapos_nn)
apply(erule redT_thread_not_disappear)
apply(auto)
done


lemma redT_preserves_wset_thread_ok:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; wset_thread_ok (wset s) (thr s) \<rbrakk> \<Longrightarrow> wset_thread_ok (wset s') (thr s')"
by(fastsimp elim!: redT.cases dest: redTWs_preserves_wset_thread_ok intro: wset_thread_ok_upd redT_updTs_preserves_wset_thread_ok)

lemma RedT_preserves_wset_thread_ok:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; wset_thread_ok (wset s) (thr s) \<rbrakk> \<Longrightarrow> wset_thread_ok (wset s') (thr s')"
by(erule (1) RedT_lift_preserveD)(erule redT_preserves_wset_thread_ok)

lemma redT_new_thread_ts_Some:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; NewThread t' x m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; wset_thread_ok ws ts \<rbrakk>
  \<Longrightarrow> ts' t' = \<lfloor>(x, no_wait_locks)\<rfloor>"
apply(erule redT_elims)
apply(auto dest: thread_oks_new_thread redT_updTs_new_thread_ts)
apply(frule (1) redT_updTs_new_thread_ts)
apply(frule (1) thread_oks_new_thread)
apply(drule (1) wset_thread_okD)
apply(drule redTWs_no_wait_thr_unchanged[where t'=t'])
apply auto
done

lemma RedT_new_thread_ts_not_None:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>;
     NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) ttas\<down>); wset_thread_ok ws ts \<rbrakk>
   \<Longrightarrow> ts' t \<noteq> None"
proof(induct rule: RedT_induct4)
  case refl thus ?case by simp
next
  case (step LS TS M WS TTAS LS' TS' M' WS' T TA LS'' TS'' M'' WS'')
  note Red = `\<langle>LS, (TS, M), WS\<rangle> -\<triangleright>TTAS\<rightarrow>* \<langle>LS', (TS', M'), WS'\<rangle>`
  note IH = `\<lbrakk> NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) TTAS\<down>); wset_thread_ok WS TS \<rbrakk> \<Longrightarrow> TS' t \<noteq> None`
  note red = `\<langle>LS', (TS', M'), WS'\<rangle> -T\<triangleright>TA\<rightarrow> \<langle>LS'', (TS'', M''), WS''\<rangle>`
  note ins = `NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) (TTAS @ [(T, TA)])\<down>)`
  note wto = `wset_thread_ok WS TS`
  from Red wto have wto': "wset_thread_ok WS' TS'" by(auto dest: RedT_preserves_wset_thread_ok)  
  show ?case
  proof(cases "NewThread t x m'' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>")
    case True thus ?thesis using red wto'
      by(auto dest!: redT_new_thread_ts_Some)
  next
    case False
    hence "NewThread t x m'' \<in> set (\<down>map (thr_a \<circ> snd) TTAS\<down>)" using ins by(auto)
    hence "TS' t \<noteq> None" using wto by(rule IH)
    with red show ?thesis
      by -(erule contrapos_nn, erule redT_thread_not_disappear)
  qed
qed

lemma redT_preserves_lock_thread_ok:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; lock_thread_ok (locks s) (thr s) \<rbrakk> \<Longrightarrow> lock_thread_ok (locks s') (thr s')"
by(auto elim!: redT_elims intro: redT_upds_preserves_lock_thread_ok acquire_all_preserves_lock_thread_ok dest!: redTWs_preserves_lock_thread_ok)

lemma RedT_preserves_lock_thread_ok:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; lock_thread_ok (locks s) (thr s) \<rbrakk> \<Longrightarrow> lock_thread_ok (locks s') (thr s')"
by(erule (1) RedT_lift_preserveD)(erule redT_preserves_lock_thread_ok)

lemma redT_ex_new_thread:
  assumes "s -t'\<triangleright>ta\<rightarrow> s'" "wset_thread_ok (wset s) (thr s)" "thr s' t = \<lfloor>(x, w)\<rfloor>" "thr s t = None"
  shows "\<exists>m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> w = no_wait_locks"
using assms
apply(cases rule: redT_elims)
apply(auto split: split_if_asm del: conjI)
apply(frule (1) wset_thread_okD)
apply(frule redTWs_no_wait_thr_unchanged[where t'=t])
apply(auto split: split_if_asm dest: redT_updTs_new_thread)
done

lemma redT_ex_new_thread':
  assumes "s -t'\<triangleright>ta\<rightarrow> s'" "thr s' t = \<lfloor>(x, w)\<rfloor>" "thr s t = None"
  shows "\<exists>m x. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
using assms
apply(cases rule: redT_elims)
apply(fastsimp split: split_if_asm dest!: redTWs_thr_None[where t'=t] redT_updTs_new_thread)+
done

end


locale multithreaded = multithreaded_base +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  assumes new_thread_memory: "\<lbrakk> t \<turnstile> s -ta\<rightarrow> s'; NewThread t' x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m = snd s'"
  and ta_Suspend_last: "t \<turnstile> s -ta\<rightarrow> s' \<Longrightarrow> Suspend w \<notin> set (butlast \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>)"
begin

lemma redT_new_thread_common:
  "\<lbrakk> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle>; NewThread t' x m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [] \<rbrakk> \<Longrightarrow> m'' = m'"
by(auto elim!: redT_elims rtrancl3p_cases dest: new_thread_memory)

lemma redT_new_thread:
  assumes "s -t'\<triangleright>ta\<rightarrow> s'" "thr s' t = \<lfloor>(x, w)\<rfloor>" "thr s t = None" "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = []"
  shows "NewThread t x (shr s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> w = no_wait_locks"
using assms
apply(cases rule: redT_elims)
apply(auto split: split_if_asm del: conjI elim!: rtrancl3p_cases)
apply(drule (2) redT_updTs_new_thread)
apply(auto dest: new_thread_memory)
done


end

end 
