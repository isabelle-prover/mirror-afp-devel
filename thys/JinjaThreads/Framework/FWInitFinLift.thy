(*  Title:      JinjaThreads/MM/FWInitFinLift.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Synthetic first and last actions for each thread} *}

theory FWInitFinLift
imports
  FWLTS
  FWLiftingSem
begin

datatype status = 
  PreStart
| Running
| Finished

abbreviation convert_TA_initial :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,status \<times> 'x,'m,'w,'o) thread_action"
where "convert_TA_initial == convert_extTA (Pair PreStart)"

lemma convert_obs_initial_convert_TA_initial: 
  "convert_obs_initial (convert_TA_initial ta) = convert_TA_initial (convert_obs_initial ta)"
by(simp add: convert_obs_initial_def)

lemma convert_TA_initial_inject [simp]:
  "convert_TA_initial ta = convert_TA_initial ta' \<longleftrightarrow> ta = ta'"
by(cases ta)(cases ta', auto)

context multithreaded_base begin

inductive init_fin :: "('l,'t,status \<times> 'x,'m,'w,'o action) semantics" ("_ \<turnstile> _ -_\<rightarrow>i _" [50,0,0,51] 51)
where
  NormalAction:
  "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> 
  \<Longrightarrow> t \<turnstile> ((Running, x), m) -convert_TA_initial (convert_obs_initial ta)\<rightarrow>i ((Running, x'), m')"

| InitialThreadAction:
  "t \<turnstile> ((PreStart, x), m) -\<lbrace>InitialThreadAction\<rbrace>\<rightarrow>i ((Running, x), m)"

| ThreadFinishAction:
  "final x \<Longrightarrow> t \<turnstile> ((Running, x), m) -\<lbrace>ThreadFinishAction\<rbrace>\<rightarrow>i ((Finished, x), m)"

primrec init_fin_final :: "status \<times> 'x \<Rightarrow> bool"
where "init_fin_final (status, x) \<longleftrightarrow> status = Finished \<and> final x"

end

declare split_paired_Ex [simp del]

inductive_simps (in multithreaded_base) init_fin_simps [simp]:
  "t \<turnstile> ((Finished, x), m) -ta\<rightarrow>i xm'"
  "t \<turnstile> ((PreStart, x), m) -ta\<rightarrow>i xm'"
  "t \<turnstile> ((Running, x), m) -ta\<rightarrow>i xm'"
  "t \<turnstile> xm -ta\<rightarrow>i ((Finished, x'), m')"
  "t \<turnstile> xm -ta\<rightarrow>i ((Running, x'), m')"
  "t \<turnstile> xm -ta\<rightarrow>i ((PreStart, x'), m')"

declare split_paired_Ex [simp]

locale if_multithreaded = multithreaded +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
begin

lemma multithreaded_init_fin: "multithreaded init_fin_final init_fin"
by(unfold_locales)(fastforce simp add: init_fin.simps convert_obs_initial_def ta_upd_simps dest: new_thread_memory)+

end

sublocale if_multithreaded < "if"!: multithreaded
  "init_fin_final"
  "init_fin"
  "map NormalAction \<circ> convert_RA"
by(rule multithreaded_init_fin)


context \<tau>multithreaded begin

inductive init_fin_\<tau>move :: "('l,'t,status \<times> 'x,'m,'w,'o action) \<tau>moves"
where
  "\<tau>move (x, m) ta (x', m') 
  \<Longrightarrow> init_fin_\<tau>move ((Running, x), m) (convert_TA_initial (convert_obs_initial ta)) ((Running, x'), m')"

lemma init_fin_\<tau>move_simps [simp]:
  "init_fin_\<tau>move ((PreStart, x), m) ta x'm' = False"
  "init_fin_\<tau>move xm ta ((PreStart, x'), m') = False"
  "init_fin_\<tau>move ((Running, x), m) ta ((s, x'), m') \<longleftrightarrow>
   (\<exists>ta'. ta = convert_TA_initial (convert_obs_initial ta') \<and> s = Running \<and> \<tau>move (x, m) ta' (x', m'))"
  "init_fin_\<tau>move ((s, x), m) ta ((Running, x'), m') \<longleftrightarrow> 
   s = Running \<and> (\<exists>ta'. ta = convert_TA_initial (convert_obs_initial ta') \<and> \<tau>move (x, m) ta' (x', m'))"
  "init_fin_\<tau>move ((Finished, x), m) ta x'm' = False"
  "init_fin_\<tau>move xm ta ((Finished, x'), m') = False"
by(simp_all add: init_fin_\<tau>move.simps)

end

locale if_\<tau>multithreaded = \<tau>multithreaded +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"

sublocale if_\<tau>multithreaded < "if"!: \<tau>multithreaded
  "init_fin_final"
  "init_fin"
  "map NormalAction \<circ> convert_RA"
  "init_fin_\<tau>move"
.

locale if_\<tau>multithreaded_wf = \<tau>multithreaded_wf +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"

sublocale if_\<tau>multithreaded_wf < if_multithreaded
by unfold_locales

sublocale if_\<tau>multithreaded_wf < if_\<tau>multithreaded .

context if_\<tau>multithreaded_wf begin

lemma \<tau>multithreaded_wf_init_fin:
  "\<tau>multithreaded_wf init_fin_final init_fin init_fin_\<tau>move"
proof(unfold_locales)
  fix t x m ta x' m'
  assume "init_fin_\<tau>move (x, m) ta (x', m')" "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" 
  thus "m = m'" by(cases)(auto dest: \<tau>move_heap)
next
  fix s ta s'
  assume "init_fin_\<tau>move s ta s'"
  thus "ta = \<epsilon>" by(cases)(auto dest: silent_tl)
qed

end

sublocale if_\<tau>multithreaded_wf < "if"!: \<tau>multithreaded_wf
  "init_fin_final"
  "init_fin"
  "map NormalAction \<circ> convert_RA"
  "init_fin_\<tau>move"
by(rule \<tau>multithreaded_wf_init_fin)


primrec init_fin_lift_inv :: "('i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> 'i \<Rightarrow> 't \<Rightarrow> status \<times> 'x \<Rightarrow> 'm \<Rightarrow> bool"
where "init_fin_lift_inv P I t (s, x) = P I t x"

locale if_lifting_inv =
  if_multithreaded +
  lifting_inv +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and P :: "'i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
begin

lemma lifting_inv_init_fin_lift_inv:
  "lifting_inv init_fin_final init_fin (init_fin_lift_inv P)"
apply(unfold_locales)
apply(fastforce elim!: init_fin.cases dest: invariant_red invariant_NewThread invariant_other)+
done

end

sublocale if_lifting_inv < "if"!: lifting_inv
  init_fin_final
  init_fin
  "map NormalAction \<circ> convert_RA"
  "init_fin_lift_inv P"
by(rule lifting_inv_init_fin_lift_inv)

primrec init_fin_lift :: "('t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> status \<times> 'x \<Rightarrow> 'm \<Rightarrow> bool"
where "init_fin_lift P t (s, x) = P t x"

locale if_lifting_wf =
  if_multithreaded +
  lifting_wf +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and P :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
begin

lemma lifting_wf_init_fin_lift:
  "lifting_wf init_fin_final init_fin (init_fin_lift P)"
apply(unfold_locales)
apply(fastforce elim!: init_fin.cases dest: dest: preserves_red preserves_other preserves_NewThread)+
done

end

sublocale if_lifting_wf < "if"!: lifting_wf 
  init_fin_final
  init_fin
  "map NormalAction \<circ> convert_RA"
  "init_fin_lift P"
by(rule lifting_wf_init_fin_lift)

lemma (in if_lifting_wf) if_lifting_inv:
  "if_lifting_inv final r (\<lambda>_::unit. P)"
proof -
  interpret lifting_inv final r convert_RA  "\<lambda>_ :: unit. P" by(rule lifting_inv)
  thus ?thesis by unfold_locales
qed

locale \<tau>lifting_inv = \<tau>multithreaded_wf +
  lifting_inv +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"
  and P :: "'i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
begin

lemma redT_silent_move_invariant:
  "\<lbrakk> \<tau>mredT s s'; ts_inv P Is (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_inv P Is (thr s') (shr s')"
by(auto dest!: redT_invariant m\<tau>move_silentD)

lemma redT_silent_moves_invariant:
  "\<lbrakk> mthr.silent_moves s s'; ts_inv P Is (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_inv P Is (thr s') (shr s')"
by(induct rule: rtranclp_induct)(auto dest: redT_silent_move_invariant)

lemma redT_\<tau>rtrancl3p_invariant:
  "\<lbrakk> mthr.\<tau>rtrancl3p s ttas s'; ts_inv P Is (thr s) (shr s) \<rbrakk>
  \<Longrightarrow> ts_inv P (upd_invs Is P (concat (map (thr_a \<circ> snd) ttas))) (thr s') (shr s')"
proof(induct arbitrary: Is rule: mthr.\<tau>rtrancl3p.induct)
  case \<tau>rtrancl3p_refl thus ?case by simp
next
  case (\<tau>rtrancl3p_step s s' tls s'' tl)
  thus ?case by(cases tl)(force dest: redT_invariant)
next
  case (\<tau>rtrancl3p_\<tau>step s s' tls s'' tl)
  thus ?case by(cases tl)(force dest: redT_invariant m\<tau>move_silentD)
qed

end

locale \<tau>lifting_wf = \<tau>multithreaded +
  lifting_wf +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"
  and P :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
begin

lemma redT_silent_move_preserves:
  "\<lbrakk> \<tau>mredT s s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
by(auto dest: redT_preserves)

lemma redT_silent_moves_preserves:
  "\<lbrakk> mthr.silent_moves s s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
by(induct rule: rtranclp.induct)(auto dest: redT_silent_move_preserves)

lemma redT_\<tau>rtrancl3p_preserves:
  "\<lbrakk> mthr.\<tau>rtrancl3p s ttas s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
by(induct rule: mthr.\<tau>rtrancl3p.induct)(auto dest: redT_silent_moves_preserves redT_preserves)

end

definition init_fin_lift_state :: "status \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,status \<times> 'x,'m,'w) state"
where "init_fin_lift_state s \<sigma> = (locks \<sigma>, (\<lambda>t. Option.map (\<lambda>(x, ln). ((s, x), ln)) (thr \<sigma> t), shr \<sigma>), wset \<sigma>, interrupts \<sigma>)"

lemma ts_ok_init_fin_lift_init_fin_lift_state [simp]:
  "ts_ok (init_fin_lift P) (thr (init_fin_lift_state s \<sigma>)) (shr (init_fin_lift_state s \<sigma>)) \<longleftrightarrow> ts_ok P (thr \<sigma>) (shr \<sigma>)"
by(auto simp add: init_fin_lift_state_def intro!: ts_okI dest: ts_okD)

lemma ts_inv_init_fin_lift_inv_init_fin_lift_state [simp]:
  "ts_inv (init_fin_lift_inv P) I (thr (init_fin_lift_state s \<sigma>)) (shr (init_fin_lift_state s \<sigma>)) \<longleftrightarrow> 
   ts_inv P I (thr \<sigma>) (shr \<sigma>)"
by(auto simp add: init_fin_lift_state_def intro!: ts_invI dest: ts_invD)

lemma init_fin_lift_state_conv_simps:
  shows shr_init_fin_lift_state: "shr (init_fin_lift_state s \<sigma>) = shr \<sigma>"
  and locks_init_fin_lift_state: "locks (init_fin_lift_state s \<sigma>) = locks \<sigma>"
  and wset_init_fin_lift_state: "wset (init_fin_lift_state s \<sigma>) = wset \<sigma>"
  and interrupts_init_fin_lift_stae: "interrupts (init_fin_lift_state s \<sigma>) = interrupts \<sigma>"
  and thr_init_fin_list_state: 
  "thr (init_fin_lift_state s \<sigma>) t = Option.map (\<lambda>(x, ln). ((s, x), ln)) (thr \<sigma> t)"
by(simp_all add: init_fin_lift_state_def)


definition lift_start_obs :: "'t \<Rightarrow> 'o list \<Rightarrow> ('t \<times> 'o action) list"
where "lift_start_obs t obs = (t, InitialThreadAction) # map (\<lambda>ob. (t, NormalAction ob)) obs"

lemma length_lift_start_obs [simp]: "length (lift_start_obs t obs) = Suc (length obs)"
by(simp add: lift_start_obs_def)

lemma set_lift_start_obs [simp]:
  "set (lift_start_obs t obs) =
   insert (t, InitialThreadAction) ((Pair t \<circ> NormalAction) ` set obs)"
by(auto simp add: lift_start_obs_def o_def)

lemma distinct_lift_start_obs [simp]: "distinct (lift_start_obs t obs) = distinct obs"
by(auto simp add: lift_start_obs_def distinct_map intro: inj_onI)

end